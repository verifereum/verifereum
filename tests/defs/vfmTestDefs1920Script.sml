open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1920";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrefoundOOG.json";
val defs = mapi (define_test "1920") tests;
val () = export_theory_no_docs ();
