open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs134";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/opcodes/push/stack_overflow.json";
val defs = mapi (define_state_test "134") tests;
val () = export_theory_no_docs ();
