open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2026";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/StackDepthLimitSEC.json";
val defs = mapi (define_test "2026") tests;
val () = export_theory_no_docs ();
