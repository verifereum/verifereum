open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs062";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/opcodes/all_opcodes/cover_revert.json";
val defs = mapi (define_state_test "062") tests;
val () = export_theory_no_docs ();
