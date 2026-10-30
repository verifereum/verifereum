Theory vfmTestDefs0037[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/top_frame_charges/top_frame_new_account_skipped_for_nonce_only_recipient.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/top_frame_charges/top_frame_new_account_skipped_for_nonce_only_recipient.json");
val defs = mapi (define_test "0037") tests;
