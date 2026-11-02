Theory vfmTestDefs2633[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcodecall_10_suicide_end/static_callcodecall_10_suicide_end.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcodecall_10_suicide_end/static_callcodecall_10_suicide_end.json");
val defs = mapi (define_test "2633") tests;
