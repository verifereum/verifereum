open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1392";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stQuadraticComplexityTest/Call20KbytesContract50_3.json";
val defs = mapi (define_test "1392") tests;
val () = export_theory_no_docs ();
