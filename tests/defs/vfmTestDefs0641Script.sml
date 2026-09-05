Theory vfmTestDefs0641[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/code_in_constructor/code_in_constructor.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/code_in_constructor/code_in_constructor.json");
val defs = mapi (define_test "0641") tests;
