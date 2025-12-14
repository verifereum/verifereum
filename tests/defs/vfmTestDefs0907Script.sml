open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0907";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/CallGoesOOGOnSecondLevel2.json";
val defs = mapi (define_test "0907") tests;
val () = export_theory_no_docs ();
