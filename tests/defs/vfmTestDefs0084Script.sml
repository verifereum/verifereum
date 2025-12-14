open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0084";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_reject_valid_full_blob_in_block_rlp.json";
val defs = mapi (define_test "0084") tests;
val () = export_theory_no_docs ();
