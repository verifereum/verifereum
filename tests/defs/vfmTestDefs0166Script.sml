open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0166";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7594_peerdas/test_max_blobs_per_tx_fork_transition.json";
val defs = mapi (define_test "0166") tests;
val () = export_theory_no_docs ();
