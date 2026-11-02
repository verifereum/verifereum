Theory vfmTestDefs0059[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/warmth_invariants/top_frame_charges_delegation_is_sender.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/warmth_invariants/top_frame_charges_delegation_is_sender.json");
val defs = mapi (define_test "0059") tests;
