Theory vfmTestDefs1864[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund600.json";
val defs = mapi (define_test "1864") tests;
