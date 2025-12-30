Theory vfmTestDefs0416[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP5656_MCOPY/MCOPY_memory_hash.json";
val defs = mapi (define_test "0416") tests;
