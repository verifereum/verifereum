open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1161";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_TransactionCALLwithData.json";
val defs = mapi (define_test "1161") tests;
val () = export_theory_no_docs ();
