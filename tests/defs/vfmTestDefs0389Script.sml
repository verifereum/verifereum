Theory vfmTestDefs0389[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3860_initcode/test_legacy_create_edge_code_size.json";
val defs = mapi (define_test "0389") tests;
