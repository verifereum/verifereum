open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0405";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/eqNonConst.json";
val defs = mapi (define_test "0405") tests;
val () = export_theory_no_docs ();
