Theory vfmTestDefs1859[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRecursiveCreate/recursiveCreate.json";
val defs = mapi (define_test "1859") tests;
