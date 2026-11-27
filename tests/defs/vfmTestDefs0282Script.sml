Theory vfmTestDefs0282[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/mpt/storage_trie_structure/extension_split_twice_same_transaction.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/mpt/storage_trie_structure/extension_split_twice_same_transaction.json");
val defs = mapi (define_test "0282") tests;
