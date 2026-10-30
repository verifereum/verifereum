Theory vfmTestDefs1123[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/account_trie_structure/delete_resurrect_delete_across_blocks.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/account_trie_structure/delete_resurrect_delete_across_blocks.json");
val defs = mapi (define_test "1123") tests;
