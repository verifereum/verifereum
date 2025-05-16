open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1936";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_0toX.json";
val defs = mapi (define_test "1936") tests;
val () = export_theory_no_docs ();
