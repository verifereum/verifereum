open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1916";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrefoundEmptyCallOOG_Paris.json";
val defs = mapi (define_test "1916") tests;
val () = export_theory_no_docs ();
