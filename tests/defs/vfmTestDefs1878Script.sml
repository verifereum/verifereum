Theory vfmTestDefs1878[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_TxToSuicideOOG.json";
val defs = mapi (define_test "1878") tests;
