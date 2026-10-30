Theory vfmTestDefs1166[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/withdrawals_trie_structure/withdrawal_leaf_embedding_boundary.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/withdrawals_trie_structure/withdrawal_leaf_embedding_boundary.json");
val defs = mapi (define_test "1166") tests;
