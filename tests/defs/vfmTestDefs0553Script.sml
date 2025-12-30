Theory vfmTestDefs0553[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcallcode_001_OOGMBefore.json";
val defs = mapi (define_test "0553") tests;
