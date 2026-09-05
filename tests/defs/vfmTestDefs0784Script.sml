Theory vfmTestDefs0784[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stExample/ranges_example/ranges_example.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stExample/ranges_example/ranges_example.json");
val defs = mapi (define_test "0784") tests;
