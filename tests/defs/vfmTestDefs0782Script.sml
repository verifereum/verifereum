Theory vfmTestDefs0782[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeSizeLimit/create2CodeSizeLimit.json";
val defs = mapi (define_test "0782") tests;
