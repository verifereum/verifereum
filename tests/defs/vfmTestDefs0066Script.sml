open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0066";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_block_blob_count.json";
val defs = mapi (define_test "0066") tests;
val () = export_theory_no_docs ();
