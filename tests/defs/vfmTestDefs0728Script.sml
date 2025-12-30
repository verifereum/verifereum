Theory vfmTestDefs0728[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecall_010_OOGE.json";
val defs = mapi (define_test "0728") tests;
