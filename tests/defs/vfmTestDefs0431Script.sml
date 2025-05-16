open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0431";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/sloadNonConst.json";
val defs = mapi (define_test "0431") tests;
val () = export_theory_no_docs ();
