open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2489";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedRemoveOwner_mySelf.json";
val defs = mapi (define_test "2489") tests;
val () = export_theory_no_docs ();
