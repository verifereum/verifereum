Theory vfmTestDefs0615[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_delegation_pointer/delegation_pointer_state_gas_on_frame_failure.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_delegation_pointer/delegation_pointer_state_gas_on_frame_failure.json");
val defs = mapi (define_test "0615") tests;
