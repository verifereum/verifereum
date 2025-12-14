open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1995";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_gasLeft.json";
val defs = mapi (define_test "1995") tests;
val () = export_theory_no_docs ();
