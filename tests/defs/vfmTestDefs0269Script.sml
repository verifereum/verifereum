Theory vfmTestDefs0269[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/mpt/storage_trie_structure/bulk_changes_in_one_depth_two_subtree.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/mpt/storage_trie_structure/bulk_changes_in_one_depth_two_subtree.json");
val defs = mapi (define_test "0269") tests;
