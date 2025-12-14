open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1991";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_XtoYtoX.json";
val defs = mapi (define_test "1991") tests;
val () = export_theory_no_docs ();
