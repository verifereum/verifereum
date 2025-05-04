open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs067";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/opcodes/push/stack_overflow.json";
val defs = mapi (define_state_test "067") tests;
val () = export_theory_no_docs ();
