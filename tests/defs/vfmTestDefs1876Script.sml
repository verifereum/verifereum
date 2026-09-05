Theory vfmTestDefs1876[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcallcallcode_001_oogm_after_2/static_callcallcallcode_001_oogm_after_2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcallcallcode_001_oogm_after_2/static_callcallcallcode_001_oogm_after_2.json");
val defs = mapi (define_test "1876") tests;
