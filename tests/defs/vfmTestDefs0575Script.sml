Theory vfmTestDefs0575[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodeDynamicCode2SelfCall.json";
val defs = mapi (define_test "0575") tests;
