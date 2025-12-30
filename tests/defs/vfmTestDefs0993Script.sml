Theory vfmTestDefs0993[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/indexesOmitExample.json";
val defs = mapi (define_test "0993") tests;
