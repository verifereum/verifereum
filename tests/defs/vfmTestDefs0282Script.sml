Theory vfmTestDefs0282[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/mpt/storage_trie_structure/insert_splits_into_extension_and_branch.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/mpt/storage_trie_structure/insert_splits_into_extension_and_branch.json");
val defs = mapi (define_test "0282") tests;
