Theory vfmTestDefs0644[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_reservoir/block_2d_gas_valid_when_cumulative_exceeds_limit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_reservoir/block_2d_gas_valid_when_cumulative_exceeds_limit.json");
val defs = mapi (define_test "0644") tests;
