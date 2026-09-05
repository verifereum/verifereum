Theory vfmTestDefs0716[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/gas_cost_berlin/gas_cost_berlin.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/gas_cost_berlin/gas_cost_berlin.json");
val defs = mapi (define_test "0716") tests;
