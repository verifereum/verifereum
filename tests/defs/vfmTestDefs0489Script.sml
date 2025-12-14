open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0489";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/codecopyNonConst.json";
val defs = mapi (define_test "0489") tests;
val () = export_theory_no_docs ();
