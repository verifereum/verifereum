Theory vfmTestDefs1859[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcall_00_ooge_1/static_callcall_00_ooge_1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcall_00_ooge_1/static_callcall_00_ooge_1.json");
val defs = mapi (define_test "1859") tests;
