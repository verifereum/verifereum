Theory vfmTestDefs0722[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/raw_balance_gas/raw_balance_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/raw_balance_gas/raw_balance_gas.json");
val defs = mapi (define_test "0722") tests;
