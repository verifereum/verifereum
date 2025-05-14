open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0916";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/CallcodeLoseGasOOG.json";
val defs = mapi (define_test "0916") tests;
val () = export_theory_no_docs ();
