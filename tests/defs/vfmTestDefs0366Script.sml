open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0366";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_to_self_destructing_account_deployed_in_same_tx.json";
val defs = mapi (define_test "0366") tests;
val () = export_theory_no_docs ();
