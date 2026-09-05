Theory vfmTestDefs2321[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts/valid_gas_pairing.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts/valid_gas_pairing.json");
val defs = mapi (define_test "2321") tests;
