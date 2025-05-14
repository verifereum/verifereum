open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0045";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/blob_txs/invalid_blob_tx_contract_creation.json";
val defs = mapi (define_test "0045") tests;
val () = export_theory_no_docs ();
