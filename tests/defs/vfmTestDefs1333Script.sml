Theory vfmTestDefs1333[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCodeCopyTest/ext_code_copy_tests_paris/ext_code_copy_tests_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCodeCopyTest/ext_code_copy_tests_paris/ext_code_copy_tests_paris.json");
val defs = mapi (define_test "1333") tests;
