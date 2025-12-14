open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2399";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorAddressTooBigRight.json";
val defs = mapi (define_test "2399") tests;
val () = export_theory_no_docs ();
