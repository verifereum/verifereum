open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0051";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/blob_txs/sufficient_balance_blob_tx_pre_fund_tx.json";
val defs = mapi (define_test "0051") tests;
val () = export_theory_no_docs ();
