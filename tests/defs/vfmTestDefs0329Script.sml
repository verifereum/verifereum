open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0329";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_invalid_transaction_after_authorization.json";
val defs = mapi (define_test "0329") tests;
val () = export_theory_no_docs ();
