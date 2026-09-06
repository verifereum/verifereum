Theory vfmTestDefs1956[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcodecallcallcode_101_suicide_end2/static_callcodecallcallcode_101_suicide_end2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcodecallcallcode_101_suicide_end2/static_callcodecallcallcode_101_suicide_end2.json");
val defs = mapi (define_test "1956") tests;
