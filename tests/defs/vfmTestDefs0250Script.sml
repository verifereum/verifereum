open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0250";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_to_non_empty_storage_non_zero_nonce.json";
val defs = mapi (define_test "0250") tests;
val () = export_theory_no_docs ();
