open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0804";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/callOutput3.json";
val defs = mapi (define_test "0804") tests;
val () = export_theory_no_docs ();
