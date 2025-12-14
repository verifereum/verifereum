open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0078";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_tx_blob_count.json";
val defs = mapi (define_test "0078") tests;
val () = export_theory_no_docs ();
