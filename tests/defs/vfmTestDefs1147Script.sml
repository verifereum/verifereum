Theory vfmTestDefs1147[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/insert_pair_sharing_one_nibble.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/insert_pair_sharing_one_nibble.json");
val defs = mapi (define_test "1147") tests;
