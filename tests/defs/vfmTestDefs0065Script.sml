open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0065";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_blob_tx_contract_creation.json";
val defs = mapi (define_test "0065") tests;
val () = export_theory_no_docs ();
