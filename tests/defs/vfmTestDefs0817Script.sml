open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0817";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecallOOGinCall.json";
val defs = mapi (define_test "0817") tests;
val () = export_theory_no_docs ();
