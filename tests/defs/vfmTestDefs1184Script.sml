Theory vfmTestDefs1184[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/osaka/eip7883_modexp_gas_increase/modexp_thresholds/modexp_variable_gas_cost_exceed_tx_gas_cap.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/osaka/eip7883_modexp_gas_increase/modexp_thresholds/modexp_variable_gas_cost_exceed_tx_gas_cap.json");
val defs = mapi (define_test "1184") tests;
