Theory vfmTestDefs1877[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_TxToSuicide.json";
val defs = mapi (define_test "1877") tests;
