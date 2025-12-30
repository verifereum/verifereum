Theory vfmTestDefs1871[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_CallA_notEnoughGasInCall.json";
val defs = mapi (define_test "1871") tests;
