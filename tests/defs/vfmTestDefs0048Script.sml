Theory vfmTestDefs0048[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/value_moving_with_tx_delegation/tx_installs_delegation_on_sender.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/value_moving_with_tx_delegation/tx_installs_delegation_on_sender.json");
val defs = mapi (define_test "0048") tests;
