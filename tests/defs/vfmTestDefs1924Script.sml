open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1924";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/TouchToEmptyAccountRevert3_Paris.json";
val defs = mapi (define_test "1924") tests;
val () = export_theory_no_docs ();
