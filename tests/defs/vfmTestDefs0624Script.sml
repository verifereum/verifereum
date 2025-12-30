Theory vfmTestDefs0624[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput1.json";
val defs = mapi (define_test "0624") tests;
