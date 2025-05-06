open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0267";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/valid_tx_invalid_auth_signature.json";
val defs = mapi (define_test "0267") tests;
val () = export_theory_no_docs ();
