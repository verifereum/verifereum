open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0797";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/CallLoseGasOOG.json";
val defs = mapi (define_test "0797") tests;
val () = export_theory_no_docs ();
