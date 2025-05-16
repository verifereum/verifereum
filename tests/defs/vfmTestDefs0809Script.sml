open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0809";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/callcodeWithHighValueAndGasOOG.json";
val defs = mapi (define_test "0809") tests;
val () = export_theory_no_docs ();
