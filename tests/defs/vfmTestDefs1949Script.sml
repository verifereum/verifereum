Theory vfmTestDefs1949[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcodecallcallcode_101_oogm_after/static_callcodecallcallcode_101_oogm_after.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcodecallcallcode_101_oogm_after/static_callcodecallcallcode_101_oogm_after.json");
val defs = mapi (define_test "1949") tests;
