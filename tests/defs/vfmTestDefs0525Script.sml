open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0525";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/xorNonConst.json";
val defs = mapi (define_test "0525") tests;
val () = export_theory_no_docs ();
