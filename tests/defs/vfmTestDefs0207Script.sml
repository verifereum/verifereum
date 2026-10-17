Theory vfmTestDefs0207[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/opcodes/data_copy_oog/calldatacopy_word_copy_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/opcodes/data_copy_oog/calldatacopy_word_copy_oog.json");
val defs = mapi (define_test "0207") tests;
