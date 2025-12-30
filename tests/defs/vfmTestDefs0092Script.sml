Theory vfmTestDefs0092[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip5656_mcopy/test_mcopy_on_empty_memory.json";
val defs = mapi (define_test "0092") tests;
