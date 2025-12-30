Theory vfmTestDefs0580[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodeInInitcodeToExistingContractWithValueTransfer.json";
val defs = mapi (define_test "0580") tests;
