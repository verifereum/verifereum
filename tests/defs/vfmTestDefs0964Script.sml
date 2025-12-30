Theory vfmTestDefs0964[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/outOfFundsOldTypes.json";
val defs = mapi (define_test "0964") tests;
