open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2483";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedConstructionNotEnoughGas.json";
val defs = mapi (define_test "2483") tests;
val () = export_theory_no_docs ();
