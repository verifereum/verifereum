Theory vfmTestDefs0989[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/add11.json";
val defs = mapi (define_test "0989") tests;
