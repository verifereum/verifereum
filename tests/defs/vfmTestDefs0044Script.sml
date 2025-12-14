open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0044";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blob_tx_attribute_opcodes.json";
val defs = mapi (define_test "0044") tests;
val () = export_theory_no_docs ();
