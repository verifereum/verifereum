Theory vfmTestDefs1516[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stExample/labels_example/labels_example.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stExample/labels_example/labels_example.json");
val defs = mapi (define_test "1516") tests;
