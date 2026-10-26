Theory vfmTestDefs0595[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_cross_frame_refund/call_frame_credit_repays_spill_before_fixed_gas_probe.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_cross_frame_refund/call_frame_credit_repays_spill_before_fixed_gas_probe.json");
val defs = mapi (define_test "0595") tests;
