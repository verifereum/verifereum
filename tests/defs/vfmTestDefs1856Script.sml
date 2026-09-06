Theory vfmTestDefs1856[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_zero_v_call_suicide/static_call_zero_v_call_suicide.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_zero_v_call_suicide/static_call_zero_v_call_suicide.json");
val defs = mapi (define_test "1856") tests;
