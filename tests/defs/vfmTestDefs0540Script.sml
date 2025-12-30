Theory vfmTestDefs0540[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcall_00_OOGE.json";
val defs = mapi (define_test "0540") tests;
