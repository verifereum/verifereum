Theory vfmTestDefs0254[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/mpt/account_trie_structure/delete_from_three_child_branch.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/mpt/account_trie_structure/delete_from_three_child_branch.json");
val defs = mapi (define_test "0254") tests;
