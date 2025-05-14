open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2574";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/TransactionDataCosts652.json";
val defs = mapi (define_test "2574") tests;
val () = export_theory_no_docs ();
