open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2519";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedConstructionNotEnoughGasPartial.json";
val defs = mapi (define_test "2519") tests;
val () = export_theory_no_docs ();
