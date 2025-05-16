open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0423";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/mulmodNonConst.json";
val defs = mapi (define_test "0423") tests;
val () = export_theory_no_docs ();
