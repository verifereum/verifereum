Theory vfmTestDefs1160[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/two_shape_changes_at_different_depths.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/two_shape_changes_at_different_depths.json");
val defs = mapi (define_test "1160") tests;
