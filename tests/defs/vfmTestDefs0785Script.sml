Theory vfmTestDefs0785[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stExample/yul_example/yul_example.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stExample/yul_example/yul_example.json");
val defs = mapi (define_test "0785") tests;
