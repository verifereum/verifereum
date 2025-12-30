Theory vfmTestDefs2582[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_TransactionCALLwithData_ToNonZeroBalance.json";
val defs = mapi (define_test "2582") tests;
