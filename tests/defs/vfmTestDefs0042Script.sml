open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0042";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/blob_txs/invalid_blob_hash_versioning_multiple_txs.json";
val defs = mapi (define_test "0042") tests;
val () = export_theory_no_docs ();
