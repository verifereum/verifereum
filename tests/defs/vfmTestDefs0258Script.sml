Theory vfmTestDefs0258[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/osaka/eip7883_modexp_gas_increase/modexp_thresholds/modexp_gas_usage_contract_wrapper.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/osaka/eip7883_modexp_gas_increase/modexp_thresholds/modexp_gas_usage_contract_wrapper.json");
val defs = mapi (define_test "0258") tests;
