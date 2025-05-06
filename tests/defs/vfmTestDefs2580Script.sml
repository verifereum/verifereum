open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2580";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransitionTest/delegatecallBeforeTransition.json";
val defs = mapi (define_test "2580") tests;
val () = export_theory_no_docs ();
