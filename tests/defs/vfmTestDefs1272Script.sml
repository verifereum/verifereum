open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1272";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stQuadraticComplexityTest/Call20KbytesContract50_1.json";
val defs = mapi (define_test "1272") tests;
val () = export_theory_no_docs ();
