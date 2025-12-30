Theory vfmTestDefs0976[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/vitalikTransactionTestParis.json";
val defs = mapi (define_test "0976") tests;
