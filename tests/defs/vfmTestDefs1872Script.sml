Theory vfmTestDefs1872[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_CallToSuicideNoStorage.json";
val defs = mapi (define_test "1872") tests;
