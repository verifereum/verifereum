open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1985";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_XtoX.json";
val defs = mapi (define_test "1985") tests;
val () = export_theory_no_docs ();
