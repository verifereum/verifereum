open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2491";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedRevokeNothing.json";
val defs = mapi (define_test "2491") tests;
val () = export_theory_no_docs ();
