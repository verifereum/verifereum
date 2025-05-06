open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0931";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecallSenderCheck.json";
val defs = mapi (define_test "0931") tests;
val () = export_theory_no_docs ();
