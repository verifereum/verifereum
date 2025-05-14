open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0410";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/extcodesizeNonConst.json";
val defs = mapi (define_test "0410") tests;
val () = export_theory_no_docs ();
