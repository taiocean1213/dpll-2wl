use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::process;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ExtendedBool {
    False,
    True,
    Undefined,
}

type Literal = i32;
type Clause = Vec<Literal>;
type CNFFormula = Vec<Clause>;
const NULL_LITERAL: Literal = 0;

struct PartialValuation {
    values: Vec<ExtendedBool>,
    trail: Vec<Literal>, // decision levels marked with 0
}

impl PartialValuation {
    fn new(n_vars: usize) -> Self {
        Self {
            values: vec![ExtendedBool::Undefined; n_vars + 1],
            trail: Vec::with_capacity(n_vars),
        }
    }

    fn assign(&mut self, lit: Literal, decision: bool) {
        let var_index = lit.abs() as usize;

        // 1. Determine the boolean assignment using a flat match on the literal's sign
        // This replaces the if/else for ExtendedBool assignment
        self.values[var_index] = match lit > 0 {
            true => ExtendedBool::True,
            false => ExtendedBool::False,
        };

        // 2. Manage the trail structure
        // We match on the 'decision' flag to determine if a marker (NULL_LITERAL)
        // is required to denote a new decision level.
        match decision {
            true => self.trail.push(NULL_LITERAL),
            false => (),
        }

        // Always record the literal on the trail
        self.trail.push(lit);
    }

    fn undo_until_decision(&mut self) -> Option<Literal> {
        let trail_length = self.trail.len();
        assert!(
            trail_length >= 1,
            "When calling this method, attribute self.trail must contain at least one element."
        );

        let mut last_flipped = None;

        // Use the correct range syntax: 0..trail_length
        for _ in 0..trail_length {
            match self.trail.pop() {
                // If we hit the marker, return the literal we just unassigned.
                // This literal is the "decision" that led to this level.
                Some(NULL_LITERAL) => return last_flipped,
                Some(lit) => {
                    let var = lit.abs() as usize;
                    self.values[var] = ExtendedBool::Undefined;
                    last_flipped = Some(lit);
                }
                None => panic!("Trail Length does not match!"),
            }
        }
        None
    }

    fn is_true(&self, lit: Literal) -> bool {
        let val = self.values[lit.abs() as usize];
        matches!(
            (lit > 0, val),
            (true, ExtendedBool::True) | (false, ExtendedBool::False)
        )
    }

    fn is_false(&self, lit: Literal) -> bool {
        let val = self.values[lit.abs() as usize];
        matches!(
            (lit > 0, val),
            (true, ExtendedBool::False) | (false, ExtendedBool::True)
        )
    }

    fn is_undef(&self, lit: Literal) -> bool {
        self.values[lit.abs() as usize] == ExtendedBool::Undefined
    }

    fn next_undef_var(&self) -> Literal {
        self.values
            .iter()
            .enumerate()
            .skip(1)
            .find(|&(_, &v)| v == ExtendedBool::Undefined)
            .map(|(i, _)| i as Literal)
            .unwrap_or(NULL_LITERAL)
    }

    fn print_model(&self) {
        for i in 1..self.values.len() {
            match self.values[i] {
                ExtendedBool::True => print!("{} ", i),
                ExtendedBool::False => print!("-{} ", i),
                ExtendedBool::Undefined => unreachable!("model must be complete"),
            }
        }
        println!();
    }
}

#[derive(Debug, PartialEq)]
enum ConflictResolution {
    Resolved,
    StillConflicting,
    RootLevelReached,
}

/// Returns true if conflict detected
#[derive(Debug)]
enum ClausePropagationStatus {
    Satisfied,
    NewWatcherFound(Literal),
    UnitClause(Literal),
    Contradiction,
}

struct DPLL {
    formula: CNFFormula,
    valuation: PartialValuation,
    watches: Vec<[Literal; 2]>,
    watch_list: HashMap<Literal, Vec<usize>>,
    initial_units: Vec<Literal>,
}

impl DPLL {
    fn new(path: &str) -> io::Result<Self> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);

        let mut n_vars = 0;
        let mut formula = Vec::new();
        let mut header_found = false;

        for line_result in reader.lines() {
            let line = line_result?.trim().to_string();

            // 1. Classify the line and the current solver state simultaneously
            // This flat match replaces all nested if/continue checks.
            match (
                line.as_str(),
                line.starts_with('c'),
                line.starts_with("p cnf"),
                header_found,
            ) {
                // Skip empty lines or comments
                ("", _, _, _) | (_, true, _, _) => (),

                // Parse the header line
                (_, _, true, _) => {
                    let parts: Vec<&str> = line.split_whitespace().collect();

                    // Nested logic is avoided by matching on the structural validity of 'parts'
                    n_vars = match parts.as_slice() {
                        [_, _, n, ..] => n.parse().map_err(|_| {
                            io::Error::new(io::ErrorKind::InvalidData, "Bad n_vars")
                        })?,
                        _ => return Err(io::Error::new(io::ErrorKind::InvalidData, "Bad header")),
                    };
                    header_found = true;
                }

                // Clause line: Only process if the header was already seen
                (_, _, false, true) => {
                    let clause: Clause = line
                        .split_whitespace()
                        .filter_map(|s| s.parse::<Literal>().ok())
                        .take_while(|&l| l != 0)
                        .collect();

                    // Only add non-empty clauses
                    match clause.is_empty() {
                        false => formula.push(clause),
                        true => (),
                    }
                }

                // Ignore any lines appearing before the header
                (_, _, false, false) => (),
            }
        }

        // 2. Final assembly of the Solver state
        let n_clauses = formula.len();
        let mut solver = Self {
            formula,
            valuation: PartialValuation::new(n_vars),
            watches: vec![[0, 0]; n_clauses],
            watch_list: HashMap::new(),
            initial_units: Vec::new(),
        };

        solver.init_watches();
        Ok(solver)
    }

    fn init_watches(&mut self) {
        for (clause_idx, clause) in self.formula.iter().enumerate() {
            // --- Stage 1: Identify Watcher Candidates ---
            // We use slice patterns to decompose the clause structure.
            // The goal is to find two distinct literals to watch.
            let candidates = match clause.as_slice() {
                // Case: The clause is empty (should not happen in valid formulas)
                [] => None,

                // Case: Explicit unit clause (exactly one literal)
                [lit] => Some((*lit, None)),

                // Case: Multiple literals. w1 is the first literal,
                // 'rest' is a slice of all subsequent literals.
                [w1, rest @ ..] => {
                    // SAT solvers require two different literals to watch.
                    // We search 'rest' for the first literal that isn't w1.
                    let w2 = rest.iter().find(|&&l| l != *w1).copied();
                    Some((*w1, w2))
                }
            };

            // --- Stage 2: Apply Watching Logic ---
            // Based on the candidates found above, we update the solver state.
            match candidates {
                // Found two distinct literals: register them both in the watch lists.
                Some((w1, Some(w2))) => {
                    self.watches[clause_idx] = [w1, w2];
                    self.watch_list.entry(w1).or_default().push(clause_idx);
                    self.watch_list.entry(w2).or_default().push(clause_idx);
                }

                // Only one unique literal exists: this is treated as a unit clause.
                // Unit clauses are added to the initial propagation queue.
                Some((w1, None)) => {
                    self.initial_units.push(w1);
                }

                // Empty clause: ignore and continue.
                None => {}
            }
        }
    }

    pub fn solve(&mut self) -> bool {
        let mut queue: Vec<Literal> = self.initial_units.clone();

        loop {
            // --- Stage 1: Unit Propagation Loop ---
            while let Some(lit) = queue.pop() {
                // Check current valuation state for the literal
                match (self.valuation.is_undef(lit), self.valuation.is_false(lit)) {
                    // Literal is already assigned: check if it contradicts the current path
                    (false, true) => {
                        match self.handle_conflict(&mut queue) {
                            false => return false, // Conflict at root level -> UNSAT
                            true => continue,      // Conflict resolved -> keep propagating
                        }
                    }
                    (false, false) => continue, // Already assigned correctly, skip

                    // Literal is unassigned: assign it and propagate the implication
                    (true, _) => {
                        self.valuation.assign(lit, false);

                        // Propagate the consequences of this assignment
                        match self.propagate(-lit, &mut queue) {
                            true => match self.handle_conflict(&mut queue) {
                                false => return false, // Propagation led to unresolvable conflict
                                true => {}             // Conflict handled, continue loop
                            },
                            false => {} // No conflict, proceed
                        }
                    }
                }
            }

            // --- Stage 2: Variable Selection (Branching) ---
            match self.valuation.next_undef_var() {
                // All variables assigned with no conflicts -> SAT
                NULL_LITERAL => return true,

                // Branch on an unassigned variable
                decision_lit => {
                    self.valuation.assign(decision_lit, true);

                    // Propagate the decision
                    match self.propagate(-decision_lit, &mut queue) {
                        true => match self.handle_conflict(&mut queue) {
                            false => return false, // Decision led to unresolvable conflict
                            true => {}             // Conflict handled, loop back to propagation
                        },
                        false => {} // No immediate conflict, loop back to propagation
                    }
                }
            }
        }
    }

    fn handle_conflict(&mut self, propagation_queue: &mut Vec<Literal>) -> bool {
        propagation_queue.clear();

        loop {
            // 1. Attempt to find the most recent decision point to flip
            let backtracking_target = self.valuation.undo_until_decision();

            // 2. Map the backtrack result to a Resolution Status
            // This closure performs the assignment and propagation in a flat pipeline
            let resolution_attempt = backtracking_target.map(|flipped_lit| {
                self.valuation.assign(-flipped_lit, false);

                match self.propagate(flipped_lit, propagation_queue) {
                    true => ConflictResolution::StillConflicting,
                    false => ConflictResolution::Resolved,
                }
            });

            // 3. Single Flat Decision Table
            // We match on the Status directly. No matches are nested inside others.
            match resolution_attempt {
                None => return false, // RootLevelReached: No more decisions to flip (UNSAT)

                Some(ConflictResolution::Resolved) => return true, // Success: Backjump complete

                Some(ConflictResolution::StillConflicting) => (), // Continue: Try next level up

                Some(ConflictResolution::RootLevelReached) => return false, // (Unreachable via map)
            }
        }
    }

    fn propagate(&mut self, falsified: Literal, propagation_queue: &mut Vec<Literal>) -> bool {
        // 1. Resolve the watch list for the falsified literal
        let Some(watch_indices) = self.watch_list.get_mut(&falsified) else {
            return false;
        };

        // Collect into a local vector to allow self-mutation during iteration
        let pending_clauses: Vec<usize> = watch_indices.drain(..).collect();

        for clause_idx in pending_clauses {
            let clause = &self.formula[clause_idx];
            let [w1, w2] = self.watches[clause_idx];
            let other_watched = match w1 == falsified {
                true => w2,
                false => w1,
            };

            // 2. Determine the status of the clause in one flat match
            let status = match clause.iter().any(|&lit| self.valuation.is_true(lit)) {
                true => ClausePropagationStatus::Satisfied,
                false => {
                    // Seek a replacement literal: not the other watch, and not false
                    let replacement = clause.iter().find(|&&lit| {
                        lit != falsified && lit != other_watched && !self.valuation.is_false(lit)
                    });

                    // Match the replacement search result against the 'other' literal's state
                    match (replacement, self.valuation.is_undef(other_watched)) {
                        (Some(&new_lit), _) => ClausePropagationStatus::NewWatcherFound(new_lit),
                        (None, true) => ClausePropagationStatus::UnitClause(other_watched),
                        (None, false) => ClausePropagationStatus::Contradiction,
                    }
                }
            };

            // 3. Single-level execution of the determined status
            match status {
                ClausePropagationStatus::Satisfied | ClausePropagationStatus::UnitClause(_) => {
                    // If satisfied or unit, we must keep watching the current falsified literal
                    self.watch_list
                        .entry(falsified)
                        .or_default()
                        .push(clause_idx);

                    // If unit, also push the implication to the queue
                    match status {
                        ClausePropagationStatus::UnitClause(lit) => propagation_queue.push(lit),
                        _ => (),
                    }
                }
                ClausePropagationStatus::NewWatcherFound(new_lit) => {
                    // Update the internal watch pair for this clause
                    let pos = match self.watches[clause_idx][0] == falsified {
                        true => 0,
                        false => 1,
                    };
                    self.watches[clause_idx][pos] = new_lit;
                    self.watch_list.entry(new_lit).or_default().push(clause_idx);
                }
                ClausePropagationStatus::Contradiction => {
                    // Restore the watch before returning to maintain solver invariants
                    self.watch_list
                        .entry(falsified)
                        .or_default()
                        .push(clause_idx);
                    return true;
                }
            }
        }

        false
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();

    // 1. Validate arguments and attempt to initialize the solver in a flat pipeline
    let initialization_result = match args.len() {
        2 => DPLL::new(&args[1]),
        _ => {
            eprintln!(
                "Usage: {} <dimacs-file>",
                args.get(0).unwrap_or(&"solver".into())
            );
            process::exit(1);
        }
    };

    // 2. Resolve the initialization status
    let mut solver = match initialization_result {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Failed to read file: {}", e);
            process::exit(1);
        }
    };

    // 3. Match on the final solver result
    match solver.solve() {
        true => {
            println!("SAT");
            solver.valuation.print_model();
        }
        false => {
            println!("UNSAT");
        }
    }
}
