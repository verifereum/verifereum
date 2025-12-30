Theory vfmTestDefs0633[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callWithHighValueOOGinCall.json";
val defs = mapi (define_test "0633") tests;
