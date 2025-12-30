Theory vfmTestDefs1881[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_multimpleSuicide.json";
val defs = mapi (define_test "1881") tests;
