Theory vfmTestDefs0017[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/byzantium/eip196_ec_add_mul/gas/invalid_gas_consumption.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/byzantium/eip196_ec_add_mul/gas/invalid_gas_consumption.json");
val defs = mapi (define_test "0017") tests;
