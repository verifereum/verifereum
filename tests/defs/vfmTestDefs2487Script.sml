open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2487";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedRemoveOwner.json";
val defs = mapi (define_test "2487") tests;
val () = export_theory_no_docs ();
