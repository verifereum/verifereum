open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1143";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemExpandingEIP150Calls/CallGoesOOGOnSecondLevel2WithMemExpandingCalls.json";
val defs = mapi (define_test "1143") tests;
val () = export_theory_no_docs ();
