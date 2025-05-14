open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0427";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/orNonConst.json";
val defs = mapi (define_test "0427") tests;
val () = export_theory_no_docs ();
