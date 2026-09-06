Theory vfmTestDefs2015[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_refund_call_a/static_refund_call_a.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_refund_call_a/static_refund_call_a.json");
val defs = mapi (define_test "2015") tests;
