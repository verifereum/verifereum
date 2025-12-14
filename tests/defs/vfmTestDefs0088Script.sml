open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0088";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_valid_blob_tx_combinations.json";
val defs = mapi (define_test "0088") tests;
val () = export_theory_no_docs ();
