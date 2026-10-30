Theory vfmTestDefs0006[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_oog/auth_state_charges_survive_dispatch_halt_with_reservoir.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_oog/auth_state_charges_survive_dispatch_halt_with_reservoir.json");
val defs = mapi (define_test "0006") tests;
