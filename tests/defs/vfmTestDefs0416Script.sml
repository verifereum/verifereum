open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0416";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/log3NonConst.json";
val defs = mapi (define_test "0416") tests;
val () = export_theory_no_docs ();
