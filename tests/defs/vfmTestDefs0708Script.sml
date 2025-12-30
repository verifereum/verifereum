Theory vfmTestDefs0708[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_SuicideMiddle.json";
val defs = mapi (define_test "0708") tests;
