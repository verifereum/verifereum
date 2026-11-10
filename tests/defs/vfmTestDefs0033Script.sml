Theory vfmTestDefs0033[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/top_frame_charges/receipt_status_top_frame_oog_between_successful_txs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/top_frame_charges/receipt_status_top_frame_oog_between_successful_txs.json");
val defs = mapi (define_test "0033") tests;
