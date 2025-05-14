open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0921";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/callOutput3.json";
val defs = mapi (define_test "0921") tests;
val () = export_theory_no_docs ();
