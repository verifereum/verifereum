Theory vfmTestDefs0746[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcall_100_OOGMAfter.json";
val defs = mapi (define_test "0746") tests;
