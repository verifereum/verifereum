Theory vfmTestDefs0717[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/gas_cost_exp/gas_cost_exp.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/gas_cost_exp/gas_cost_exp.json");
val defs = mapi (define_test "0717") tests;
