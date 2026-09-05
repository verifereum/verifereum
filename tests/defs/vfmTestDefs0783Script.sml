Theory vfmTestDefs0783[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stExample/merge_test/merge_test.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stExample/merge_test/merge_test.json");
val defs = mapi (define_test "0783") tests;
