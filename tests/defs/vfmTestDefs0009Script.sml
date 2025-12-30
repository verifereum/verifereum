Theory vfmTestDefs0009[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/byzantium/eip198_modexp_precompile/test_modexp.json";
val defs = mapi (define_test "0009") tests;
