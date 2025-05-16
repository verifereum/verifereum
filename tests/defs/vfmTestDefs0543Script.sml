open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0543";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callWithHighValueAndGasOOG.json";
val defs = mapi (define_test "0543") tests;
val () = export_theory_no_docs ();
