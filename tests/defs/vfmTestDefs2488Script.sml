open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2488";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedRemoveOwnerByNonOwner.json";
val defs = mapi (define_test "2488") tests;
val () = export_theory_no_docs ();
