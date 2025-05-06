open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0039";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/blob_txs/blob_type_tx_pre_fork.json";
val defs = mapi (define_test "0039") tests;
val () = export_theory_no_docs ();
