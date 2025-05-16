open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2362";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorAddressTooBigRight.json";
val defs = mapi (define_test "2362") tests;
val () = export_theory_no_docs ();
