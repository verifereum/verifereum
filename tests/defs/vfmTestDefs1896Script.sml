Theory vfmTestDefs1896[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_zero_value_call_oog_revert/static_zero_value_call_oog_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_zero_value_call_oog_revert/static_zero_value_call_oog_revert.json");
val defs = mapi (define_test "1896") tests;
