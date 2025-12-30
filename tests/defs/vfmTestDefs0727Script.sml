Theory vfmTestDefs0727[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecall_010.json";
val defs = mapi (define_test "0727") tests;
