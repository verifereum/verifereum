Theory vfmTestDefs1136[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/delete_inline_leaf_survivor_stays_inline.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/delete_inline_leaf_survivor_stays_inline.json");
val defs = mapi (define_test "1136") tests;
