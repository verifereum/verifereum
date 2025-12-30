Theory vfmTestDefs1861[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund50_1.json";
val defs = mapi (define_test "1861") tests;
