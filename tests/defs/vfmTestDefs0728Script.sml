Theory vfmTestDefs0728[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/raw_ext_code_size_gas/raw_ext_code_size_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/raw_ext_code_size_gas/raw_ext_code_size_gas.json");
val defs = mapi (define_test "0728") tests;
