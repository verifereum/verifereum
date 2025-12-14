open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0041";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blob_gas_subtraction_tx.json";
val defs = mapi (define_test "0041") tests;
val () = export_theory_no_docs ();
