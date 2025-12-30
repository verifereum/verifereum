Theory vfmTestDefs0579[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodeInInitcodeToExistingContract.json";
val defs = mapi (define_test "0579") tests;
