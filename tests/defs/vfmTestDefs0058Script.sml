open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0058";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/excess_blob_gas/correct_decreasing_blob_gas_costs.json";
val defs = mapi (define_test "0058") tests;
val () = export_theory_no_docs ();
