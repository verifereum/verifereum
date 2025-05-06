open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2599";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedIsOwnerFalse.json";
val defs = mapi (define_test "2599") tests;
val () = export_theory_no_docs ();
