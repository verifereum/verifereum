open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0248";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_multiple_valid_authorization_tuples_first_invalid_same_signer.json";
val defs = mapi (define_test "0248") tests;
val () = export_theory_no_docs ();
