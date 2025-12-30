Theory vfmTestDefs0157[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/istanbul/eip1344_chainid/test_chainid.json";
val defs = mapi (define_test "0157") tests;
