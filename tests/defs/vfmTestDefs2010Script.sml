Theory vfmTestDefs2010[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_loop_calls_depth_then_revert/static_loop_calls_depth_then_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_loop_calls_depth_then_revert/static_loop_calls_depth_then_revert.json");
val defs = mapi (define_test "2010") tests;
