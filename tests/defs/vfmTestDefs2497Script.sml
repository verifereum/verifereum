open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2497";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletConstructionOOG.json";
val defs = mapi (define_test "2497") tests;
val () = export_theory_no_docs ();
