open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0880";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/CallRecursiveBombPreCall.json";
val defs = mapi (define_test "0880") tests;
val () = export_theory_no_docs ();
