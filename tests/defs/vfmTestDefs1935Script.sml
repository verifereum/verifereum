open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1935";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_0to0toX.json";
val defs = mapi (define_test "1935") tests;
val () = export_theory_no_docs ();
