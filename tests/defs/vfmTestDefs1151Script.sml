Theory vfmTestDefs1151[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/insert_splits_nested_extension_first_nibble.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/insert_splits_nested_extension_first_nibble.json");
val defs = mapi (define_test "1151") tests;
