Theory vfmTestDefs0750[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcall_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0750") tests;
