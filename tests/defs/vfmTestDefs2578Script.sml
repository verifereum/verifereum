open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2578";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransitionTest/delegatecallAfterTransition.json";
val defs = mapi (define_test "2578") tests;
val () = export_theory_no_docs ();
