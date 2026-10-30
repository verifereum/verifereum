Theory vfmTestDefs0540[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_calldata_floor/calldata_floor_charged_to_sender.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_calldata_floor/calldata_floor_charged_to_sender.json");
val defs = mapi (define_test "0540") tests;
