Theory vfmTestDefs2298[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRefundTest/refund_tx_to_suicide/refund_tx_to_suicide.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRefundTest/refund_tx_to_suicide/refund_tx_to_suicide.json");
val defs = mapi (define_test "2298") tests;
