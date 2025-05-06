open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0925";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecallBasic.json";
val defs = mapi (define_test "0925") tests;
val () = export_theory_no_docs ();
