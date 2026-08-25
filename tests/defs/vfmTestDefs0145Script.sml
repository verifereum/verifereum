Theory vfmTestDefs0145[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/opcodes/test_value_transfer_gas_calculation_homestead.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/opcodes/test_value_transfer_gas_calculation_homestead.json");
val defs = mapi (define_test "0145") tests;
