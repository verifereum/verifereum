open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1404";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stQuadraticComplexityTest/Return50000.json";
val defs = mapi (define_test "1404") tests;
val () = export_theory_no_docs ();
