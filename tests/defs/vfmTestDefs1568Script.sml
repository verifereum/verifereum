Theory vfmTestDefs1568[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stLogTests/log3_empty_mem/log3_empty_mem.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stLogTests/log3_empty_mem/log3_empty_mem.json");
val defs = mapi (define_test "1568") tests;
