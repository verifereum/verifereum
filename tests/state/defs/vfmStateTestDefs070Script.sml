open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs070";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/homestead/coverage/coverage/coverage.json";
val defs = mapi (define_state_test "070") tests;
val () = export_theory_no_docs ();
