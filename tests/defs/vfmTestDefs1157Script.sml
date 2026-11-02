Theory vfmTestDefs1157[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/restructure_two_disjoint_paths_same_block.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/restructure_two_disjoint_paths_same_block.json");
val defs = mapi (define_test "1157") tests;
