open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0333";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_pointer_call_followed_by_direct_call.json";
val defs = mapi (define_test "0333") tests;
val () = export_theory_no_docs ();
