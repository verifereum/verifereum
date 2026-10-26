Theory vfmTestDefs2278[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRefundTest/refund50_1/refund50_1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRefundTest/refund50_1/refund50_1.json");
val defs = mapi (define_test "2278") tests;
