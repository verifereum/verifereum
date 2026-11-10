Theory vfmTestDefs0538[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_calldata_floor/calldata_floor_binds_regardless_of_funding.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_calldata_floor/calldata_floor_binds_regardless_of_funding.json");
val defs = mapi (define_test "0538") tests;
