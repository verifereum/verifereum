Theory vfmTestDefs1985[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_check_opcodes3/static_check_opcodes3.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_check_opcodes3/static_check_opcodes3.json");
val defs = mapi (define_test "1985") tests;
