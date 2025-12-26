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
        let var = lit.abs() as usize;
        self.values[var] = if lit > 0 {
            ExtendedBool::True
        } else {
            ExtendedBool::False
        };
        if decision {
            self.trail.push(NULL_LITERAL);
        }
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

        for line in reader.lines() {
            let line = line?.trim().to_string();
            if line.is_empty() || line.starts_with('c') {
                continue;
            }
            if line.starts_with("p cnf") {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() < 4 {
                    return Err(io::Error::new(io::ErrorKind::InvalidData, "Bad header"));
                }
                n_vars = parts[2]
                    .parse()
                    .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "Bad n_vars"))?;
                header_found = true;
                continue;
            }
            if !header_found {
                continue;
            }
            let clause: Clause = line
                .split_whitespace()
                .filter_map(|s| s.parse::<Literal>().ok())
                .take_while(|&l| l != 0)
                .collect();
            if !clause.is_empty() {
                formula.push(clause);
            }
        }

        let n_clauses = formula.len();
        let mut solver = Self {
            formula,
            valuation: PartialValuation::new(n_vars),
            watches: vec![[0, 0]; n_clauses], // use length before move
            watch_list: HashMap::new(),
            initial_units: Vec::new(),
        };
        solver.init_watches();
        Ok(solver)
    }

    fn init_watches(&mut self) {
        for (clause_idx, clause) in self.formula.iter().enumerate() {
            if clause.is_empty() {
                continue;
            }
            if clause.len() == 1 {
                self.initial_units.push(clause[0]);
                continue;
            }
            // Pick first two literals
            let w1 = clause[0];
            let mut w2 = clause[1];
            if clause.len() > 2 && w1 == w2 {
                // find a different one
                for &lit in clause.iter().skip(2) {
                    if lit != w1 {
                        w2 = lit;
                        break;
                    }
                }
            }
            if w1 == w2 {
                // all literals the same → unit clause
                self.initial_units.push(w1);
                continue;
            }
            self.watches[clause_idx] = [w1, w2];
            self.watch_list.entry(w1).or_default().push(clause_idx);
            self.watch_list.entry(w2).or_default().push(clause_idx);
        }
    }

    pub fn solve(&mut self) -> bool {
        let mut queue: Vec<Literal> = self.initial_units.clone();

        loop {
            while let Some(lit) = queue.pop() {
                let is_assigned = !self.valuation.is_undef(lit);
                if is_assigned {
                    let is_already_false = self.valuation.is_false(lit);
                    if is_already_false {
                        if !self.handle_conflict(&mut queue) {
                            return false;
                        }
                    }
                    continue;
                }
                self.valuation.assign(lit, false);

                // Capture the result of the propagation attempt
                let found_conflict = self.propagate(-lit, &mut queue);
                if found_conflict {
                    // Define the resolution status
                    let is_resolvable = self.handle_conflict(&mut queue);

                    // If the conflict cannot be resolved (e.g., at root level),
                    // the formula is UNSAT
                    if !is_resolvable {
                        return false;
                    }
                }
            }

            // Selection: Identify the next branching point
            let next_var = self.valuation.next_undef_var();

            // If no variables are left to assign, the current model satisfies the formula
            if next_var == NULL_LITERAL {
                return true; // Satisfiable (SAT)
            }

            // 2. Decision: Branch on the selected literal
            let decision_lit = next_var;
            self.valuation.assign(decision_lit, true);

            // 3. Propagation: Check if the opposite assignment causes a contradiction
            let propagation_found_conflict = self.propagate(-decision_lit, &mut queue);

            if propagation_found_conflict {
                // 4. Resolution: Attempt to recover from the conflict (e.g., via backjumping)
                let is_recoverable = self.handle_conflict(&mut queue);

                // If the conflict is at the root level, no solution exists
                if !is_recoverable {
                    return false; // Unsatisfiable (UNSAT)
                }
            }
        }
    }

    fn handle_conflict(&mut self, queue: &mut Vec<Literal>) -> bool {
        queue.clear();
        loop {
            let Some(flipped) = self.valuation.undo_until_decision() else {
                return false; // UNSAT
            };
            let flip_lit = -flipped;
            self.valuation.assign(flip_lit, false);
            if !self.propagate(flipped, queue) {
                return true; // resolved
            }
            // else conflict, backtrack further
        }
    }

    /// Returns true if conflict detected
    fn propagate(&mut self, falsified: Literal, queue: &mut Vec<Literal>) -> bool {
        let Some(clauses_to_process) = self.watch_list.get_mut(&falsified) else {
            return false;
        };

        // Drain all clauses watching this literal into a local vec
        let pending: Vec<usize> = clauses_to_process.drain(..).collect();

        for clause_idx in pending {
            let clause = &self.formula[clause_idx];

            if clause.iter().any(|&lit| self.valuation.is_true(lit)) {
                // Clause satisfied — keep watching falsified
                self.watch_list
                    .entry(falsified)
                    .or_default()
                    .push(clause_idx);
                continue;
            }

            let watched = &mut self.watches[clause_idx];
            let falsified_idx = if watched[0] == falsified { 0 } else { 1 };
            let other = watched[1 - falsified_idx];

            // Try to find a new watch literal
            let mut found_new = false;
            for &lit in clause {
                if lit == falsified || lit == other {
                    continue;
                }
                if !self.valuation.is_false(lit) {
                    watched[falsified_idx] = lit;
                    self.watch_list.entry(lit).or_default().push(clause_idx);
                    found_new = true;
                    break;
                }
            }

            if found_new {
                continue;
            }

            // Could not find new watch
            if self.valuation.is_undef(other) {
                queue.push(other);
                // Still keep watching falsified
                self.watch_list
                    .entry(falsified)
                    .or_default()
                    .push(clause_idx);
            } else {
                // Conflict!
                // Put back the clause so it's not lost
                self.watch_list
                    .entry(falsified)
                    .or_default()
                    .push(clause_idx);
                return true;
            }
        }

        false
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <dimacs-file>", args[0]);
        process::exit(1);
    }

    let mut solver = match DPLL::new(&args[1]) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Failed to read file: {}", e);
            process::exit(1);
        }
    };

    if solver.solve() {
        println!("SAT");
        solver.valuation.print_model();
    } else {
        println!("UNSAT");
    }
}
