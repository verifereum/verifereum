Theory vfmTestDefs0539[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcall_00.json";
val defs = mapi (define_test "0539") tests;
