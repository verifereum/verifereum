open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0058";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_fork_transition_excess_blob_gas_at_blob_genesis.json";
val defs = mapi (define_test "0058") tests;
val () = export_theory_no_docs ();
