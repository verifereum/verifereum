Theory vfmTestDefs0268[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/mpt/storage_trie_structure/branch_rebuilt_with_other_child_across_blocks.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/mpt/storage_trie_structure/branch_rebuilt_with_other_child_across_blocks.json");
val defs = mapi (define_test "0268") tests;
