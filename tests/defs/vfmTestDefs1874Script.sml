Theory vfmTestDefs1874[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_CallToSuicideTwice.json";
val defs = mapi (define_test "1874") tests;
