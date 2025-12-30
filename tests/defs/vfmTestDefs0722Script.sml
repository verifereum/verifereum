Theory vfmTestDefs0722[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcallcode_001_SuicideMiddle.json";
val defs = mapi (define_test "0722") tests;
