Theory vfmTestDefs2287[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRefundTest/refund_call_to_suicide_twice/refund_call_to_suicide_twice.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRefundTest/refund_call_to_suicide_twice/refund_call_to_suicide_twice.json");
val defs = mapi (define_test "2287") tests;
