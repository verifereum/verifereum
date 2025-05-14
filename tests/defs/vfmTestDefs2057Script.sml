open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2057";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_0toXtoX.json";
val defs = mapi (define_test "2057") tests;
val () = export_theory_no_docs ();
