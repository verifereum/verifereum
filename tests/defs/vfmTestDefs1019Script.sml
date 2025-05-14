open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1019";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP2930/transactionCosts.json";
val defs = mapi (define_test "1019") tests;
val () = export_theory_no_docs ();
