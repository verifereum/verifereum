Theory vfmTestDefs1867[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refundSSTORE.json";
val defs = mapi (define_test "1867") tests;
