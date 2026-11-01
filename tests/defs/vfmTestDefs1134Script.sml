Theory vfmTestDefs1134[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/delete_from_block_built_trie.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/delete_from_block_built_trie.json");
val defs = mapi (define_test "1134") tests;
