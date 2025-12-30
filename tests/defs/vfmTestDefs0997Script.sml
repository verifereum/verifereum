Theory vfmTestDefs0997[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/rangesExample.json";
val defs = mapi (define_test "0997") tests;
