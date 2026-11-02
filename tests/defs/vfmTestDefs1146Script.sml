Theory vfmTestDefs1146[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/insert_leaf_into_empty_trie.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/insert_leaf_into_empty_trie.json");
val defs = mapi (define_test "1146") tests;
