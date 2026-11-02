Theory vfmTestDefs0828[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/sstore_refunds/sstore_clear_then_rewrite_zero_grants_refund_once.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/sstore_refunds/sstore_clear_then_rewrite_zero_grants_refund_once.json");
val defs = mapi (define_test "0828") tests;
