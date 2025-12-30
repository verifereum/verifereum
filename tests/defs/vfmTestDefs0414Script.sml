Theory vfmTestDefs0414[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP5656_MCOPY/MCOPY_copy_cost.json";
val defs = mapi (define_test "0414") tests;
