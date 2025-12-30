Theory vfmTestDefs2044[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/CallInfiniteLoop.json";
val defs = mapi (define_test "2044") tests;
