Theory vfmTestDefs2288[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRefundTest/refund_change_non_zero_storage/refund_change_non_zero_storage.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRefundTest/refund_change_non_zero_storage/refund_change_non_zero_storage.json");
val defs = mapi (define_test "2288") tests;
