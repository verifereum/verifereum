Theory vfmTestDefs0721[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/gas_cost_return/gas_cost_return.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/gas_cost_return/gas_cost_return.json");
val defs = mapi (define_test "0721") tests;
