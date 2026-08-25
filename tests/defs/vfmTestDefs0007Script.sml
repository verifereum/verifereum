Theory vfmTestDefs0007[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/byzantium/eip196_ec_add_mul/test_gas_costs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/byzantium/eip196_ec_add_mul/test_gas_costs.json");
val defs = mapi (define_test "0007") tests;
