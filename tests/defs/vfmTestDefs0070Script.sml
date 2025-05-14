open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0070";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/excess_blob_gas/invalid_zero_excess_blob_gas_in_header.json";
val defs = mapi (define_test "0070") tests;
val () = export_theory_no_docs ();
