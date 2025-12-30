Theory vfmTestDefs0632[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callWithHighValueAndOOGatTxLevel.json";
val defs = mapi (define_test "0632") tests;
