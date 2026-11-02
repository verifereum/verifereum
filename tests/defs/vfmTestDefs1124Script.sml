Theory vfmTestDefs1124[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/account_trie_structure/genesis_extension_and_branch.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/account_trie_structure/genesis_extension_and_branch.json");
val defs = mapi (define_test "1124") tests;
