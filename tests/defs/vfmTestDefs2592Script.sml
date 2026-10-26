Theory vfmTestDefs2592[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcallcode_01_2/static_callcallcode_01_2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcallcode_01_2/static_callcallcode_01_2.json");
val defs = mapi (define_test "2592") tests;
