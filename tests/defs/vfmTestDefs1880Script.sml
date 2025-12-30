Theory vfmTestDefs1880[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_getEtherBack.json";
val defs = mapi (define_test "1880") tests;
