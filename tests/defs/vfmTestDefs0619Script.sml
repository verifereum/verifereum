open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0619";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/CallLoseGasOOG.json";
val defs = mapi (define_test "0619") tests;
val () = export_theory_no_docs ();
