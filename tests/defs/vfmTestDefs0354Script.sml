open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0354";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_multiple_first_valid_authorization_tuples_same_signer.json";
val defs = mapi (define_test "0354") tests;
val () = export_theory_no_docs ();
