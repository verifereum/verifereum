Theory vfmTestDefs0201[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/opcodes/data_copy_oog/codecopy_word_copy_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/opcodes/data_copy_oog/codecopy_word_copy_oog.json");
val defs = mapi (define_test "0201") tests;
