Theory vfmTestDefs0159[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/istanbul/eip152_blake2/test_blake2b.json";
val defs = mapi (define_test "0159") tests;
