open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2363";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorMemOOGAndInsufficientBalance.json";
val defs = mapi (define_test "2363") tests;
val () = export_theory_no_docs ();
