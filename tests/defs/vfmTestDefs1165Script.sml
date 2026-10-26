Theory vfmTestDefs1165[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/withdrawals_trie_structure/withdrawal_branch_mixes_embedded_and_hashed.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/withdrawals_trie_structure/withdrawal_branch_mixes_embedded_and_hashed.json");
val defs = mapi (define_test "1165") tests;
