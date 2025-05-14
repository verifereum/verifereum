open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2582";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransitionTest/delegatecallAfterTransition.json";
val defs = mapi (define_test "2582") tests;
val () = export_theory_no_docs ();
