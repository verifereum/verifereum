Theory vfmTestDefs1919[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcallcodecallcode_011_suicide_middle2/static_callcallcodecallcode_011_suicide_middle2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcallcodecallcode_011_suicide_middle2/static_callcallcodecallcode_011_suicide_middle2.json");
val defs = mapi (define_test "1919") tests;
