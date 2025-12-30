Theory vfmTestDefs0255[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_precompile_before_fork.json";
val defs = mapi (define_test "0255") tests;
