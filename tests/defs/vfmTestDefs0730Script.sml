Theory vfmTestDefs0730[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecall_010_OOGMBefore.json";
val defs = mapi (define_test "0730") tests;
