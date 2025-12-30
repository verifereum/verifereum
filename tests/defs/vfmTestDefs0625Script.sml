Theory vfmTestDefs0625[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput2.json";
val defs = mapi (define_test "0625") tests;
