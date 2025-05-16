open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0800";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/Delegatecall1024.json";
val defs = mapi (define_test "0800") tests;
val () = export_theory_no_docs ();
