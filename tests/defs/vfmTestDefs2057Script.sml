Theory vfmTestDefs2057[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/TestStoreGasPrices.json";
val defs = mapi (define_test "2057") tests;
