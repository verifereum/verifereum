open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0492";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/divNonConst.json";
val defs = mapi (define_test "0492") tests;
val () = export_theory_no_docs ();
