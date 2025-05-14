open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2612";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletChangeRequirementRemovePendingTransaction.json";
val defs = mapi (define_test "2612") tests;
val () = export_theory_no_docs ();
