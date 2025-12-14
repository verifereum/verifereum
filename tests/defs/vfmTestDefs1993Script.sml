open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1993";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_XtoYtoZ.json";
val defs = mapi (define_test "1993") tests;
val () = export_theory_no_docs ();
