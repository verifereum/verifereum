Theory vfmTestDefs0744[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcall_100.json";
val defs = mapi (define_test "0744") tests;
