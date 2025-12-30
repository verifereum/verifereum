Theory vfmTestDefs0705[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_OOGMAfter.json";
val defs = mapi (define_test "0705") tests;
