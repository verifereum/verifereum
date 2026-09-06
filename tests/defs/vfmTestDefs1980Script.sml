Theory vfmTestDefs1980[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_calldelcode_01_ooge/static_calldelcode_01_ooge.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_calldelcode_01_ooge/static_calldelcode_01_ooge.json");
val defs = mapi (define_test "1980") tests;
