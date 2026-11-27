Theory vfmTestDefs0261[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/mpt/account_trie_structure/insert_splits_extension_above_deep_branch.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/mpt/account_trie_structure/insert_splits_extension_above_deep_branch.json");
val defs = mapi (define_test "0261") tests;
