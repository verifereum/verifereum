open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0666";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callcodeWithHighValueAndGasOOG.json";
val defs = mapi (define_test "0666") tests;
val () = export_theory_no_docs ();
