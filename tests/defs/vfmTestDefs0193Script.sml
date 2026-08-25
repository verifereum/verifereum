Theory vfmTestDefs0193[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_modexp_variable_gas_cost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7883_modexp_gas_increase/test_modexp_variable_gas_cost.json");
val defs = mapi (define_test "0193") tests;
