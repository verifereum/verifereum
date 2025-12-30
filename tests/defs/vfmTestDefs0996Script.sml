Theory vfmTestDefs0996[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/mergeTest.json";
val defs = mapi (define_test "0996") tests;
