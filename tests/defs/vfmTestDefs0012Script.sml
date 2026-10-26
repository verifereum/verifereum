Theory vfmTestDefs0012[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_oog/recipient_charge_oog_rolls_back_delegations.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_oog/recipient_charge_oog_rolls_back_delegations.json");
val defs = mapi (define_test "0012") tests;
