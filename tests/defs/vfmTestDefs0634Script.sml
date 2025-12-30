Theory vfmTestDefs0634[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callcodeOutput1.json";
val defs = mapi (define_test "0634") tests;
