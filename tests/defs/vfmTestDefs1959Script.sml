open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1959";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSelfBalance/selfBalanceCallTypes.json";
val defs = mapi (define_test "1959") tests;
val () = export_theory_no_docs ();
