open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1401";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stQuadraticComplexityTest/Return50000_2.json";
val defs = mapi (define_test "1401") tests;
val () = export_theory_no_docs ();
