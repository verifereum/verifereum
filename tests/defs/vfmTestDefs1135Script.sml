Theory vfmTestDefs1135[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/delete_from_genesis_trie.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/delete_from_genesis_trie.json");
val defs = mapi (define_test "1135") tests;
