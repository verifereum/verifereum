open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1940";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_0toXtoY.json";
val defs = mapi (define_test "1940") tests;
val () = export_theory_no_docs ();
