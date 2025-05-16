open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2370";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorZeorSizeMemExpansion.json";
val defs = mapi (define_test "2370") tests;
val () = export_theory_no_docs ();
