open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0397";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/balanceNonConst.json";
val defs = mapi (define_test "0397") tests;
val () = export_theory_no_docs ();
