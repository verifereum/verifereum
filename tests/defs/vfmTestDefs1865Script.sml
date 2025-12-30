Theory vfmTestDefs1865[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refundFF.json";
val defs = mapi (define_test "1865") tests;
