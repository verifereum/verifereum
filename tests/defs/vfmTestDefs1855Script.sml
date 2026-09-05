Theory vfmTestDefs1855[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_with_high_value_oo_gin_call/static_call_with_high_value_oo_gin_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_with_high_value_oo_gin_call/static_call_with_high_value_oo_gin_call.json");
val defs = mapi (define_test "1855") tests;
