Theory vfmTestDefs1863[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund50percentCap.json";
val defs = mapi (define_test "1863") tests;
