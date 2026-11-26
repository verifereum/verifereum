Theory vfmTestDefs0270[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/mpt/storage_trie_structure/bulk_changes_under_full_root_branch.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/mpt/storage_trie_structure/bulk_changes_under_full_root_branch.json");
val defs = mapi (define_test "0270") tests;
