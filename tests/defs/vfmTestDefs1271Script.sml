open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1271";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stQuadraticComplexityTest/Call1MB1024Calldepth.json";
val defs = mapi (define_test "1271") tests;
val () = export_theory_no_docs ();
