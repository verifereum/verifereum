open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0062";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/excess_blob_gas/invalid_excess_blob_gas_above_target_change.json";
val defs = mapi (define_test "0062") tests;
val () = export_theory_no_docs ();
