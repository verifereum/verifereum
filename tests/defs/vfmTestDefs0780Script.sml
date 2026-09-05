Theory vfmTestDefs0780[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stExample/indexes_omit_example/indexes_omit_example.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stExample/indexes_omit_example/indexes_omit_example.json");
val defs = mapi (define_test "0780") tests;
