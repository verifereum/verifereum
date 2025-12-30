Theory vfmTestDefs0238[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_eip_2537.json";
val defs = mapi (define_test "0238") tests;
