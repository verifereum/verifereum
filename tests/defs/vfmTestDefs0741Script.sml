Theory vfmTestDefs0741[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecall_10.json";
val defs = mapi (define_test "0741") tests;
