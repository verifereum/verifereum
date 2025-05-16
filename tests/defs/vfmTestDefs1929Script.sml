open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1929";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/InitCollisionNonZeroNonce.json";
val defs = mapi (define_test "1929") tests;
val () = export_theory_no_docs ();
