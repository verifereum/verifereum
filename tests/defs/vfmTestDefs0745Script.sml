Theory vfmTestDefs0745[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcall_100_OOGE.json";
val defs = mapi (define_test "0745") tests;
