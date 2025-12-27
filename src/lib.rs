use std::fs::File;
use std::io::{BufRead, BufReader, Result};

type Literal = i32;

pub struct Clause {
    pub literals: Vec<Literal>,
    pub watched_indices: [usize; 2],
    pub visit_count: usize,
}

impl Clause {
    fn find_replacement_watch(&self, assignments: &[Option<bool>]) -> Option<usize> {
        self.literals
            .iter()
            .enumerate()
            .position(|(idx, &candidate)| {
                idx != self.watched_indices[0]
                    && idx != self.watched_indices[1]
                    && Solver::get_literal_value(assignments, candidate) != Some(false)
            })
    }
}

struct PropagationState<'a> {
    assignments: &'a mut [Option<bool>],
    watch_lists: &'a mut Vec<Vec<usize>>,
    propagation_queue: &'a mut Vec<Literal>,
}

pub struct Solver {
    pub clauses: Vec<Clause>,
    pub assignments: Vec<Option<bool>>,
    pub watch_lists: Vec<Vec<usize>>,
}

impl Solver {
    pub fn new(path: &str) -> Result<Self> {
        let mut variable_count = 0;
        let mut clauses = Vec::new();
        let lines = BufReader::new(File::open(path)?)
            .lines()
            .map_while(Result::ok);

        for line in lines {
            Self::parse_dimacs_line(line, &mut variable_count, &mut clauses);
        }

        let mut solver = Self {
            clauses,
            assignments: vec![None; variable_count + 1],
            watch_lists: vec![Vec::new(); (variable_count + 1) * 2],
        };

        solver.initialize_watches();
        Ok(solver)
    }

    #[inline]
    pub fn lit_to_var(lit: Literal) -> usize {
        lit.abs() as usize
    }
    #[inline]
    pub fn lit_to_idx(lit: Literal) -> usize {
        (lit.abs() as usize * 2) + (lit < 0) as usize
    }
    #[inline]
    fn make_lit(var: usize, polarity: bool) -> Literal {
        if polarity { var as i32 } else { -(var as i32) }
    }

    fn parse_dimacs_line(line: String, variable_count: &mut usize, clauses: &mut Vec<Clause>) {
        if line.starts_with('c') || line.is_empty() {
            return;
        }
        if line.starts_with("p cnf") {
            *variable_count = line
                .split_whitespace()
                .nth(2)
                .and_then(|s| s.parse().ok())
                .unwrap_or(0);
            return;
        }
        let literals: Vec<Literal> = line
            .split_whitespace()
            .filter_map(|s| s.parse().ok())
            .take_while(|&val| val != 0)
            .collect();
        let len = literals.len();

        // Fix: Use saturating logic to ensure indices are 0 even if len is 0.
        // The solve() method will handle the actual UNSAT logic for empty clauses.
        clauses.push(Clause {
            literals,
            watched_indices: [0, 1.min(len.saturating_sub(1))],
            visit_count: 0,
        });
    }

    fn initialize_watches(&mut self) {
        for (id, c) in self.clauses.iter().enumerate() {
            // Only add to watch lists if the clause actually has literals
            if let Some(&lit0) = c.literals.get(c.watched_indices[0]) {
                self.watch_lists[Self::lit_to_idx(lit0)].push(id);
            }
            if c.literals.len() > 1 {
                let lit1 = c.literals[c.watched_indices[1]];
                self.watch_lists[Self::lit_to_idx(lit1)].push(id);
            }
        }
    }

    #[inline]
    pub fn get_literal_value(assignments: &[Option<bool>], lit: Literal) -> Option<bool> {
        assignments[Self::lit_to_var(lit)].map(|val| val == (lit > 0))
    }

    pub fn propagate(&mut self, satisfied_lit: Literal) -> bool {
        let mut queue = vec![satisfied_lit];
        while let Some(l) = queue.pop() {
            if !self.process_watch_list(l, &mut queue) {
                return false;
            }
        }
        true
    }

    fn assign_and_propagate(&mut self, lit: Literal) -> bool {
        match Self::get_literal_value(&self.assignments, lit) {
            Some(false) => false,
            Some(true) => true,
            None => {
                self.assignments[Self::lit_to_var(lit)] = Some(lit > 0);
                self.propagate(lit)
            }
        }
    }

    fn process_watch_list(&mut self, satisfied_lit: Literal, queue: &mut Vec<Literal>) -> bool {
        let falsified_idx = Self::lit_to_idx(-satisfied_lit);
        let mut affected = std::mem::take(&mut self.watch_lists[falsified_idx]);
        let mut conflict = false;

        let mut state = PropagationState {
            assignments: &mut self.assignments,
            watch_lists: &mut self.watch_lists,
            propagation_queue: queue,
        };

        affected.retain(|&cid| {
            if conflict {
                return true;
            }
            let (keep, is_conflict) =
                Self::update_clause(&mut self.clauses[cid], -satisfied_lit, cid, &mut state);
            conflict = is_conflict;
            keep
        });

        self.watch_lists[falsified_idx].extend(affected);
        !conflict
    }

    fn update_clause(
        c: &mut Clause,
        falsified: Literal,
        cid: usize,
        state: &mut PropagationState,
    ) -> (bool, bool) {
        c.visit_count += 1;

        // Ensure the falsified literal is at index 1
        if c.literals[c.watched_indices[0]] == falsified {
            c.watched_indices.swap(0, 1);
        }

        let w0 = c.literals[c.watched_indices[0]];
        if Self::get_literal_value(state.assignments, w0) == Some(true) {
            return (true, false);
        }

        if let Some(j) = c.find_replacement_watch(state.assignments) {
            c.watched_indices[1] = j;
            state.watch_lists[Self::lit_to_idx(c.literals[j])].push(cid);
            return (false, false);
        }

        match Self::get_literal_value(state.assignments, w0) {
            Some(false) => (true, true),
            None => {
                state.assignments[Self::lit_to_var(w0)] = Some(w0 > 0);
                state.propagation_queue.push(w0);
                (true, false)
            }
            _ => (true, false),
        }
    }

    pub fn solve(&mut self) -> bool {
        // Fix: Explicitly check for empty clauses (UNSAT)
        if self.clauses.iter().any(|c| c.literals.is_empty()) {
            return false;
        }

        let units: Vec<Literal> = self
            .clauses
            .iter()
            .filter(|c| c.literals.len() == 1)
            .map(|c| c.literals[0])
            .collect();

        if units.into_iter().any(|l| !self.assign_and_propagate(l)) {
            return false;
        }
        self.solve_recursive()
    }

    fn solve_recursive(&mut self) -> bool {
        let var_to_assign = self
            .assignments
            .iter()
            .enumerate()
            .skip(1)
            .find(|(_, a)| a.is_none())
            .map(|(i, _)| i);

        let Some(var) = var_to_assign else {
            return true;
        };

        for polarity in [true, false] {
            let old_assignments = self.assignments.clone();
            let old_watches = self.watch_lists.clone();

            if self.assign_and_propagate(Self::make_lit(var, polarity)) {
                if self.solve_recursive() {
                    return true;
                }
            }

            self.assignments = old_assignments;
            self.watch_lists = old_watches;
        }
        false
    }

    pub fn print_model(&self) {
        for (i, &a) in self.assignments.iter().enumerate().skip(1) {
            if let Some(val) = a {
                print!("{}{i} ", if val { "" } else { "-" });
            }
        }
        println!("0");
    }
}
