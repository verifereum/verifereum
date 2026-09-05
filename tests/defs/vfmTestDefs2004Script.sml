Theory vfmTestDefs2004[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_log1_empty_mem/static_log1_empty_mem.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_log1_empty_mem/static_log1_empty_mem.json");
val defs = mapi (define_test "2004") tests;
