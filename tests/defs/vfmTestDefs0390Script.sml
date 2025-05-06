open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0390";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/addNonConst.json";
val defs = mapi (define_test "0390") tests;
val () = export_theory_no_docs ();
