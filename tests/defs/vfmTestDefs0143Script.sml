Theory vfmTestDefs0143[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/opcodes/test_value_transfer_gas_calculation.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/opcodes/test_value_transfer_gas_calculation.json");
val defs = mapi (define_test "0143") tests;
