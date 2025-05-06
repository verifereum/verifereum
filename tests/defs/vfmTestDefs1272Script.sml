open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1272";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_TransactionCALL_ToEmpty_Paris.json";
val defs = mapi (define_test "1272") tests;
val () = export_theory_no_docs ();
