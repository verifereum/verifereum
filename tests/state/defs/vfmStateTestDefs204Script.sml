open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs204";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/homestead/coverage/coverage/coverage.json";
val defs = mapi (define_state_test "204") tests;
val () = export_theory_no_docs ();
