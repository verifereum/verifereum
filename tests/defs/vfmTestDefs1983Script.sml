open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1983";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_Xto0toXto0.json";
val defs = mapi (define_test "1983") tests;
val () = export_theory_no_docs ();
