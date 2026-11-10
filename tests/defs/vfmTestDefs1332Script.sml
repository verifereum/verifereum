Theory vfmTestDefs1332[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCodeCopyTest/ext_code_copy_target_range_longer_than_code_tests/ext_code_copy_target_range_longer_than_code_tests.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCodeCopyTest/ext_code_copy_target_range_longer_than_code_tests/ext_code_copy_target_range_longer_than_code_tests.json");
val defs = mapi (define_test "1332") tests;
