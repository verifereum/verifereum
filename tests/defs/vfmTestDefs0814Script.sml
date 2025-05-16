open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0814";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecallInInitcodeToEmptyContract.json";
val defs = mapi (define_test "0814") tests;
val () = export_theory_no_docs ();
