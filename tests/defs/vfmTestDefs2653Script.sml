Theory vfmTestDefs2653[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcodecallcallcode_101_ooge/static_callcodecallcallcode_101_ooge.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcodecallcallcode_101_ooge/static_callcodecallcallcode_101_ooge.json");
val defs = mapi (define_test "2653") tests;
