open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1106";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemExpandingEIP150Calls/CallGoesOOGOnSecondLevelWithMemExpandingCalls.json";
val defs = mapi (define_test "1106") tests;
val () = export_theory_no_docs ();
