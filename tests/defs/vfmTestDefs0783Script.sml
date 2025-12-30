Theory vfmTestDefs0783[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeSizeLimit/createCodeSizeLimit.json";
val defs = mapi (define_test "0783") tests;
