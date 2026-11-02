Theory vfmTestDefs1125[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/account_trie_structure/genesis_full_branch_arity_sixteen.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/account_trie_structure/genesis_full_branch_arity_sixteen.json");
val defs = mapi (define_test "1125") tests;
