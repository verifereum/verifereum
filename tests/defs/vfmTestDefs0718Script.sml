Theory vfmTestDefs0718[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/gas_cost_jump/gas_cost_jump.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/gas_cost_jump/gas_cost_jump.json");
val defs = mapi (define_test "0718") tests;
