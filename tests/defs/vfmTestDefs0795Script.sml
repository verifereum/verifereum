open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0795";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/Call1024OOG.json";
val defs = mapi (define_test "0795") tests;
val () = export_theory_no_docs ();
