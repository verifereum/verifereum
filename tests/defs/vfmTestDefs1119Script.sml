Theory vfmTestDefs1119[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/account_trie_structure/code_hash_flip_with_account_shape_change.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/account_trie_structure/code_hash_flip_with_account_shape_change.json");
val defs = mapi (define_test "1119") tests;
