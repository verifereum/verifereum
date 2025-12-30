Theory vfmTestDefs0666[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcallcode_01.json";
val defs = mapi (define_test "0666") tests;
