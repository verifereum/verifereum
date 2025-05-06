open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2609";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletConfirm.json";
val defs = mapi (define_test "2609") tests;
val () = export_theory_no_docs ();
