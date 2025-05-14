open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2595";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedChangeOwner_fromNotOwner.json";
val defs = mapi (define_test "2595") tests;
val () = export_theory_no_docs ();
