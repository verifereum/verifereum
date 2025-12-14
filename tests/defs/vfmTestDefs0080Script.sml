open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0080";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_zero_excess_blob_gas_in_header.json";
val defs = mapi (define_test "0080") tests;
val () = export_theory_no_docs ();
