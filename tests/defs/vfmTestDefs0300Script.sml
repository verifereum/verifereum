Theory vfmTestDefs0300[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/mpt/storage_trie_structure/leaf_replaced_by_two_siblings.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/mpt/storage_trie_structure/leaf_replaced_by_two_siblings.json");
val defs = mapi (define_test "0300") tests;
