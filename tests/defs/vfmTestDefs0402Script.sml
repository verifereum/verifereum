open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0402";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/createNonConst.json";
val defs = mapi (define_test "0402") tests;
val () = export_theory_no_docs ();
