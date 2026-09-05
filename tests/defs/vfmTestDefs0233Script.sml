Theory vfmTestDefs0233[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/istanbul/eip2200_net_gas_metering/sstore_combinations/sstore_combinations_initial_staticcall_only.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/istanbul/eip2200_net_gas_metering/sstore_combinations/sstore_combinations_initial_staticcall_only.json");
val defs = mapi (define_test "0233") tests;
