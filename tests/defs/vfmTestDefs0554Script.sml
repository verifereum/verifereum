Theory vfmTestDefs0554[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_create/create2_failed_deposit_refunds_storage_state_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_create/create2_failed_deposit_refunds_storage_state_gas.json");
val defs = mapi (define_test "0554") tests;
