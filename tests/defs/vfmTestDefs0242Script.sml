Theory vfmTestDefs0242[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_invalid_gas_g2msm.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_invalid_gas_g2msm.json");
val defs = mapi (define_test "0242") tests;
