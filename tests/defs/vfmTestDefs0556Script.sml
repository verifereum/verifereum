Theory vfmTestDefs0556[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcallcode_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0556") tests;
