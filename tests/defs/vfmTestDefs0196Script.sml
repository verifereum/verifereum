Theory vfmTestDefs0196[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_vectors_from_legacy_tests.json";
val defs = mapi (define_test "0196") tests;
