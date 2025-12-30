Theory vfmTestDefs0252[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_invalid_zero_length_g2msm.json";
val defs = mapi (define_test "0252") tests;
