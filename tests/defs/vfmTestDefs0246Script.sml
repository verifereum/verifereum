Theory vfmTestDefs0246[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_invalid_length_pairing.json";
val defs = mapi (define_test "0246") tests;
