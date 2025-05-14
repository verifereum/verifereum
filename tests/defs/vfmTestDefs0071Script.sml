open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0071";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/excess_blob_gas_fork_transition/fork_transition_excess_blob_gas_at_blob_genesis.json";
val defs = mapi (define_test "0071") tests;
val () = export_theory_no_docs ();
