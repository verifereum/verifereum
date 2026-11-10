Theory vfmTestDefs2566[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcall_00_ooge_2/static_callcall_00_ooge_2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcall_00_ooge_2/static_callcall_00_ooge_2.json");
val defs = mapi (define_test "2566") tests;
