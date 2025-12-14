open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0353";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_max_depth_call_stack.json";
val defs = mapi (define_test "0353") tests;
val () = export_theory_no_docs ();
