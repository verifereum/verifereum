open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0055";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_correct_excess_blob_gas_calculation.json";
val defs = mapi (define_test "0055") tests;
val () = export_theory_no_docs ();
