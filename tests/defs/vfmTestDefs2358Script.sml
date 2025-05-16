open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2358";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallRecursiveBombLog.json";
val defs = mapi (define_test "2358") tests;
val () = export_theory_no_docs ();
