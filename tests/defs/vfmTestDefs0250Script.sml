Theory vfmTestDefs0250[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/mpt/account_trie_structure/account_deleted_and_recreated_same_block.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/mpt/account_trie_structure/account_deleted_and_recreated_same_block.json");
val defs = mapi (define_test "0250") tests;
