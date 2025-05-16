open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2546";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_TransactionCALLwithData_ToEmpty_Paris.json";
val defs = mapi (define_test "2546") tests;
val () = export_theory_no_docs ();
