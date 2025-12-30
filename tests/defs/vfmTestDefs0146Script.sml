Theory vfmTestDefs0146[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/precompiles/test_precompile_absence.json";
val defs = mapi (define_test "0146") tests;
