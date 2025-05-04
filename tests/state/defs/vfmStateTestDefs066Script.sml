open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs066";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/opcodes/push/push.json";
val defs = mapi (define_state_test "066") tests;
val () = export_theory_no_docs ();
