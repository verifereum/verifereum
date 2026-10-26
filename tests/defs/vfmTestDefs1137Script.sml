Theory vfmTestDefs1137[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/delete_missing_is_noop.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/delete_missing_is_noop.json");
val defs = mapi (define_test "1137") tests;
