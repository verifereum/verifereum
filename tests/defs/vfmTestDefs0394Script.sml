open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0394";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/andNonConst.json";
val defs = mapi (define_test "0394") tests;
val () = export_theory_no_docs ();
