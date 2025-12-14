open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0049";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blobhash_multiple_txs_in_block.json";
val defs = mapi (define_test "0049") tests;
val () = export_theory_no_docs ();
