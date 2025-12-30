Theory vfmTestDefs0090[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip5656_mcopy/test_mcopy_huge_memory_expansion.json";
val defs = mapi (define_test "0090") tests;
