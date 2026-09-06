Theory vfmTestDefs1851[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_value_inherit_from_call/static_call_value_inherit_from_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_value_inherit_from_call/static_call_value_inherit_from_call.json");
val defs = mapi (define_test "1851") tests;
