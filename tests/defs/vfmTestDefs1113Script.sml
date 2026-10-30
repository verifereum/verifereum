Theory vfmTestDefs1113[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/istanbul/eip2200_net_gas_metering/sstore_combinations/sstore_combinations_initial.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/istanbul/eip2200_net_gas_metering/sstore_combinations/sstore_combinations_initial.json");
val defs = mapi (define_test "1113") tests;
