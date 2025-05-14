open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0648";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/CallLoseGasOOG.json";
val defs = mapi (define_test "0648") tests;
val () = export_theory_no_docs ();
