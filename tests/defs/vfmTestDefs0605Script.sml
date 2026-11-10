Theory vfmTestDefs0605[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_cross_frame_refund/cross_frame_refund_with_reservoir_grant.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_cross_frame_refund/cross_frame_refund_with_reservoir_grant.json");
val defs = mapi (define_test "0605") tests;
