open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0409";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/extcodecopyNonConst.json";
val defs = mapi (define_test "0409") tests;
val () = export_theory_no_docs ();
