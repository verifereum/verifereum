Theory vfmTestDefs0008[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_oog/auth_state_gas_in_header_on_dispatch_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_oog/auth_state_gas_in_header_on_dispatch_revert.json");
val defs = mapi (define_test "0008") tests;
