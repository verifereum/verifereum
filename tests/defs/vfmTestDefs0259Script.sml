Theory vfmTestDefs0259[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_valid_gas_pairing.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_valid_gas_pairing.json");
val defs = mapi (define_test "0259") tests;
