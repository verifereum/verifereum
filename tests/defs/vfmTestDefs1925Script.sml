open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1925";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/TouchToEmptyAccountRevert_Paris.json";
val defs = mapi (define_test "1925") tests;
val () = export_theory_no_docs ();
