open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2475";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedChangeOwner.json";
val defs = mapi (define_test "2475") tests;
val () = export_theory_no_docs ();
