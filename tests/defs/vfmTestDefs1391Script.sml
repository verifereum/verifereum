open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1391";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stQuadraticComplexityTest/Call50000_identity.json";
val defs = mapi (define_test "1391") tests;
val () = export_theory_no_docs ();
