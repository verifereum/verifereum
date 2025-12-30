Theory vfmTestDefs0231[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_wycheproof_extra.json";
val defs = mapi (define_test "0231") tests;
