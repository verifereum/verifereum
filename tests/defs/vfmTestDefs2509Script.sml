open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2509";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedAddOwnerAddMyself.json";
val defs = mapi (define_test "2509") tests;
val () = export_theory_no_docs ();
