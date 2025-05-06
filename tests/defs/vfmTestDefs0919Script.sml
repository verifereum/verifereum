open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0919";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/callOutput3partialFail.json";
val defs = mapi (define_test "0919") tests;
val () = export_theory_no_docs ();
