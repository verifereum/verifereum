Theory vfmTestDefs0052[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/warmth_invariants/intrinsic_charges_recipient_is_coinbase.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/warmth_invariants/intrinsic_charges_recipient_is_coinbase.json");
val defs = mapi (define_test "0052") tests;
