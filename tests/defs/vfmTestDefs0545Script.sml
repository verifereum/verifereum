Theory vfmTestDefs0545[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcall_000_OOGMAfter.json";
val defs = mapi (define_test "0545") tests;
