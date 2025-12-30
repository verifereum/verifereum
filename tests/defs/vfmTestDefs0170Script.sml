Theory vfmTestDefs0170[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7823_modexp_upper_bounds/test_modexp_upper_bounds.json";
val defs = mapi (define_test "0170") tests;
