Theory vfmTestDefs1155[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/one_to_sixteen_into_committed_leaf.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/one_to_sixteen_into_committed_leaf.json");
val defs = mapi (define_test "1155") tests;
