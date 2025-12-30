Theory vfmTestDefs0550[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcallcode_001.json";
val defs = mapi (define_test "0550") tests;
