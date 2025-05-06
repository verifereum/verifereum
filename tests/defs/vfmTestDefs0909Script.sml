open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0909";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/Call1024PreCalls.json";
val defs = mapi (define_test "0909") tests;
val () = export_theory_no_docs ();
