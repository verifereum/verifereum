open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1285";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stQuadraticComplexityTest/QuadraticComplexitySolidity_CallDataCopy.json";
val defs = mapi (define_test "1285") tests;
val () = export_theory_no_docs ();
