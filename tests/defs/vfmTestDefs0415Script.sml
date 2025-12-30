Theory vfmTestDefs0415[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP5656_MCOPY/MCOPY_memory_expansion_cost.json";
val defs = mapi (define_test "0415") tests;
