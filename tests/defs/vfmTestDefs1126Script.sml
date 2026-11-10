Theory vfmTestDefs1126[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/account_trie_structure/insert_full_branch_during_execution.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/account_trie_structure/insert_full_branch_during_execution.json");
val defs = mapi (define_test "1126") tests;
