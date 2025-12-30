Theory vfmTestDefs2074[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStackTests/shallowStack.json";
val defs = mapi (define_test "2074") tests;
