use cnf_dpll_2wl::Solver;
use std::io::Write;
use tempfile::NamedTempFile;

fn run_cnf(content: &str, expected: bool) {
    let mut file = NamedTempFile::new().unwrap();
    write!(file, "{}", content).unwrap();
    let path = file.path().to_str().unwrap();

    let mut solver = Solver::new(path).expect("Failed to load CNF");
    let result = solver.solve();

    assert_eq!(result, expected, "Failed on CNF:\n{}", content);
}

#[test]
fn empty_formula() {
    run_cnf("p cnf 0 0\n", true);
}

#[test]
fn single_var_no_clauses() {
    run_cnf("p cnf 1 0\n", true);
}

#[test]
fn unit_positive() {
    run_cnf("p cnf 1 1\n1 0\n", true);
}

#[test]
fn unit_negative() {
    run_cnf("p cnf 1 1\n-1 0\n", true);
}

#[test]
fn empty_clause() {
    run_cnf("p cnf 0 1\n0\n", false);
}

#[test]
fn contradictory_units() {
    run_cnf("p cnf 1 2\n1 0\n-1 0\n", false);
}

#[test]
fn simple_propagation() {
    run_cnf("p cnf 3 3\n1 2 0\n-1 3 0\n-2 -3 0\n", true);
}

#[test]
fn pigeonhole() {
    run_cnf("p cnf 2 3\n1 2 0\n-1 0\n-2 0\n", false);
}

#[test]
fn horn_sat() {
    run_cnf("p cnf 3 3\n-1 -2 3 0\n1 0\n2 0\n", true);
}

#[test]
fn backtrack_unsat() {
    run_cnf("p cnf 3 4\n1 2 0\n1 -2 0\n-1 3 0\n-3 0\n", false);
}

#[test]
fn tautologies() {
    run_cnf("p cnf 2 2\n1 -1 0\n2 -2 0\n", true);
}

#[test]
fn deep_unsat() {
    run_cnf(
        "p cnf 4 7\n1 2 0\n-1 3 0\n-2 -3 4 0\n-4 0\n-1 0\n2 0\n3 0\n",
        false,
    );
}

#[test]
fn chain_with_backtrack() {
    run_cnf(
        "p cnf 5 7\n1 2 3 0\n-1 -2 4 0\n-3 -4 5 0\n-5 0\n1 0\n-2 0\n-3 0\n",
        true,
    );
}

#[test]
fn test_2wl_watcher_movement() {
    // 1 2 3 0
    // If we set 1=false, watcher should move from 1 to 3.
    // If we then set 2=false, 3 must be detected as unit via the 2WL mechanism.
    run_cnf("p cnf 3 2\n1 2 3 0\n-1 0\n-2 0\n", true);
}

#[test]
fn test_2wl_skip_satisfied() {
    // 1 2 3 0
    // If 1 is true, the clause is satisfied.
    // If 2 is then set to false, 2WL should skip this clause
    // and NOT look for a new watcher because it's already satisfied by 1.
    run_cnf("p cnf 3 2\n1 2 3 0\n1 0\n-2 0\n", true);
}

#[test]
fn test_2wl_non_chronological_logic() {
    // A more complex case where watchers are forced to shift multiple times
    // Clause: 1 2 3 4 5
    // Sequence: -5, -4, -3 (watchers move), then -2 (2 becomes unit)
    run_cnf(
        "p cnf 5 5\n1 2 3 4 5 0\n-5 0\n-4 0\n-3 0\n-1 0\n",
        true, // 2 should be forced true
    );
}

#[test]
fn test_2wl_conflict_at_last_literal() {
    // 1 2 0
    // Set 1=false, 2=false. 2WL must detect that no new watcher exists
    // and the other watched literal (which is also false) causes a conflict.
    run_cnf("p cnf 2 3\n1 2 0\n-1 0\n-2 0\n", false);
}

#[test]
fn test_2wl_long_clause_unit_propagation() {
    // Tests if 2WL correctly identifies the last literal in a long clause
    run_cnf(
        "p cnf 10 10\n1 2 3 4 5 6 7 8 9 10 0\n-1 0\n-2 0\n-3 0\n-4 0\n-5 0\n-6 0\n-7 0\n-8 0\n-9 0\n",
        true,
    );
}

#[test]
fn test_2wl_mechanism_proof() {
    let mut file = tempfile::NamedTempFile::new().unwrap();
    writeln!(file, "p cnf 5 1\n1 2 3 4 5 0").unwrap();

    let mut solver = Solver::new(file.path().to_str().unwrap()).unwrap();

    // Specify the type as i32 to allow calculations
    let lits_to_falsify: [i32; 3] = [-3, -4, -5];

    for &l in &lits_to_falsify {
        // DRY/SST FIX: Use the new assignments field and helper methods
        solver.assignments[Solver::lit_to_var(l)] = Some(l > 0);
        solver.propagate(l);
    }

    assert_eq!(
        solver.clauses[0].visit_count, 0,
        "Clause visited for unwatched literal!"
    );

    // Falsify watched literal 1
    let lit1: i32 = -1;
    solver.assignments[1] = Some(false);
    solver.propagate(lit1);

    assert_eq!(
        solver.clauses[0].visit_count, 1,
        "Clause not visited for watched literal!"
    );
}
