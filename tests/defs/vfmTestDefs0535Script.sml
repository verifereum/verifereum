open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0535";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/CallcodeLoseGasOOG.json";
val defs = mapi (define_test "0535") tests;
val () = export_theory_no_docs ();
