Theory vfmTestDefs1879[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_changeNonZeroStorage.json";
val defs = mapi (define_test "1879") tests;
