Theory vfmTestDefs0549[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcall_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0549") tests;
