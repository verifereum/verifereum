Theory vfmTestDefs0259[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_valid_gas_pairing.json";
val defs = mapi (define_test "0259") tests;
