open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0063";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_blob_hash_versioning_multiple_txs.json";
val defs = mapi (define_test "0063") tests;
val () = export_theory_no_docs ();
