Theory vfmTestDefs1159[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/shared_node_deleted_in_one_trie.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/shared_node_deleted_in_one_trie.json");
val defs = mapi (define_test "1159") tests;
