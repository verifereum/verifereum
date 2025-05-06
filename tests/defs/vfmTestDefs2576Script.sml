open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2576";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransitionTest/createNameRegistratorPerTxsAt.json";
val defs = mapi (define_test "2576") tests;
val () = export_theory_no_docs ();
