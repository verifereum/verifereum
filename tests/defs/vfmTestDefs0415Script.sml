open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0415";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/log2NonConst.json";
val defs = mapi (define_test "0415") tests;
val () = export_theory_no_docs ();
