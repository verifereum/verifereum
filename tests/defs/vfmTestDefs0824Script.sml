open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0824";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/CallGoesOOGOnSecondLevel.json";
val defs = mapi (define_test "0824") tests;
val () = export_theory_no_docs ();
