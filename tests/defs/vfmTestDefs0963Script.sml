Theory vfmTestDefs0963[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/outOfFunds.json";
val defs = mapi (define_test "0963") tests;
