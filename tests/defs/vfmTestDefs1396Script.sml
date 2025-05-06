open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1396";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stQuadraticComplexityTest/Create1000.json";
val defs = mapi (define_test "1396") tests;
val () = export_theory_no_docs ();
