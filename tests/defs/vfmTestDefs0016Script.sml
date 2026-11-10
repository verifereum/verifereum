Theory vfmTestDefs0016[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_oog/reservoir_settlement_with_value_to_empty_recipient.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_oog/reservoir_settlement_with_value_to_empty_recipient.json");
val defs = mapi (define_test "0016") tests;
