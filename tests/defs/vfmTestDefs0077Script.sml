open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0077";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_static_excess_blob_gas_from_zero_on_blobs_above_target.json";
val defs = mapi (define_test "0077") tests;
val () = export_theory_no_docs ();
