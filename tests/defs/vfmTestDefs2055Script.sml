Theory vfmTestDefs2055[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/TestKeywords.json";
val defs = mapi (define_test "2055") tests;
