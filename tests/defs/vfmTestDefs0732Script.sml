Theory vfmTestDefs0732[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecall_010_SuicideMiddle.json";
val defs = mapi (define_test "0732") tests;
