Theory vfmTestDefs1833[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_ripemd160_4_gas719/static_call_ripemd160_4_gas719.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_ripemd160_4_gas719/static_call_ripemd160_4_gas719.json");
val defs = mapi (define_test "1833") tests;
