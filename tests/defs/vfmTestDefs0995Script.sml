Theory vfmTestDefs0995[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/labelsExample.json";
val defs = mapi (define_test "0995") tests;
