use assert_cmd::Command;
use predicates::prelude::*;

// Helper function to run the solver on a specific file path
fn run_solver(file_path: &str) -> Command {
    let mut cmd = Command::cargo_bin("dpll-2wl").unwrap();
    // Pass the example file as the first command-line argument
    cmd.arg(format!("examples/{}", file_path));
    cmd
}

#[test]
fn test_aim_sat_example() {
    // Expected output for this specific SAT file is "SAT" followed by a valuation
    run_solver("aim-50-1_6-yes1-4.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("SAT"));
}

#[test]
fn test_hole6_sat_example() {
    // Expected output for 'hole6.cnf' is "UNSAT"
    run_solver("hole6.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("SAT"));
}

#[test]
fn test_simple_sat_example() {
    run_solver("test-SAT.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("SAT"));
}

#[test]
fn test_simple_unsat_example() {
    run_solver("test-UNSAT.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("UNSAT"));
}

#[test]
fn test_sudoku_puzzle() {
    // Sudoku puzzles encoded in CNF usually have a solution (SAT)
    run_solver("sudoku.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("SAT"));
}

#[test]
fn test_zebra_puzzle() {
    // The famous Zebra puzzle has a unique solution (SAT)
    run_solver("zebra.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("SAT"));
}
