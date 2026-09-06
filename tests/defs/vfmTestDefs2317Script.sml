Theory vfmTestDefs2317[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts/invalid_zero_length_g2msm.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts/invalid_zero_length_g2msm.json");
val defs = mapi (define_test "2317") tests;
