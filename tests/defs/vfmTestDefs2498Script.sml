open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2498";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletConstructionPartial.json";
val defs = mapi (define_test "2498") tests;
val () = export_theory_no_docs ();
