Theory vfmTestDefs2016[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_refund_call_to_suicide_no_storage/static_refund_call_to_suicide_no_storage.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_refund_call_to_suicide_no_storage/static_refund_call_to_suicide_no_storage.json");
val defs = mapi (define_test "2016") tests;
