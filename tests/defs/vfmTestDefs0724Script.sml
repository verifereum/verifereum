Theory vfmTestDefs0724[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcode_01.json";
val defs = mapi (define_test "0724") tests;
