Theory vfmTestDefs0965[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/senderBalance.json";
val defs = mapi (define_test "0965") tests;
