open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0165";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7594_peerdas/test_invalid_max_blobs_per_tx.json";
val defs = mapi (define_test "0165") tests;
val () = export_theory_no_docs ();
