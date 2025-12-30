Theory vfmTestDefs0147[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/precompiles/test_precompiles.json";
val defs = mapi (define_test "0147") tests;
