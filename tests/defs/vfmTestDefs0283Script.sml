Theory vfmTestDefs0283[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/mpt/storage_trie_structure/insert_after_unchanged_subtree_two_nibbles_deep.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/mpt/storage_trie_structure/insert_after_unchanged_subtree_two_nibbles_deep.json");
val defs = mapi (define_test "0283") tests;
