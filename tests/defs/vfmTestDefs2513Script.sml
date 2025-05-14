open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2513";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/createWithInvalidOpcode.json";
val defs = mapi (define_test "2513") tests;
val () = export_theory_no_docs ();
