Theory vfmTestDefs0779[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeSizeLimit/codesizeInit.json";
val defs = mapi (define_test "0779") tests;
