open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1928";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSLoadTest/sloadGasCost.json";
val defs = mapi (define_test "1928") tests;
val () = export_theory_no_docs ();
