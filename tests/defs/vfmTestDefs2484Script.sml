open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2484";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedConstructionNotEnoughGasPartial.json";
val defs = mapi (define_test "2484") tests;
val () = export_theory_no_docs ();
