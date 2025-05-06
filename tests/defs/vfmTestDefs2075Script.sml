open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2075";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSelfBalance/selfBalanceGasCost.json";
val defs = mapi (define_test "2075") tests;
val () = export_theory_no_docs ();
