open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2492";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/balanceInputAddressTooBig.json";
val defs = mapi (define_test "2492") tests;
val () = export_theory_no_docs ();
