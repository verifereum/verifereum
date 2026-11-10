Theory vfmTestDefs0833[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/sstore_refunds_revert/sstore_clear_refund_discarded_on_frame_failure.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/sstore_refunds_revert/sstore_clear_refund_discarded_on_frame_failure.json");
val defs = mapi (define_test "0833") tests;
