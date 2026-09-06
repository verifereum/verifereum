Theory vfmTestDefs0724[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/raw_call_gas_ask/raw_call_gas_ask.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/raw_call_gas_ask/raw_call_gas_ask.json");
val defs = mapi (define_test "0724") tests;
