open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0074";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/excess_blob_gas_fork_transition/invalid_pre_fork_block_with_blob_fields.json";
val defs = mapi (define_test "0074") tests;
val () = export_theory_no_docs ();
