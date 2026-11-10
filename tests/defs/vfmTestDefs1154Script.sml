Theory vfmTestDefs1154[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/mpt/storage_trie_structure/mass_delete_sixteen_to_one.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/mpt/storage_trie_structure/mass_delete_sixteen_to_one.json");
val defs = mapi (define_test "1154") tests;
