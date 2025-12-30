Theory vfmTestDefs0640[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callcodeWithHighValue.json";
val defs = mapi (define_test "0640") tests;
