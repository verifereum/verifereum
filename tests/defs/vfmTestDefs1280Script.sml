open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1280";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stQuadraticComplexityTest/Call50000_sha256.json";
val defs = mapi (define_test "1280") tests;
val () = export_theory_no_docs ();
