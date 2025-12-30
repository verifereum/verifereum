Theory vfmTestDefs0992[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/eip1559.json";
val defs = mapi (define_test "0992") tests;
