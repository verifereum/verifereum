open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs137";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/precompiles/precompile_absence/precompile_absence.json";
val defs = mapi (define_state_test "137") tests;
val () = export_theory_no_docs ();
