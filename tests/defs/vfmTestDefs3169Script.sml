Theory vfmTestDefs3169[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/spurious_dragon/eip161_state_trie_clearing/touched_account_emptiness/call_new_account_charge_after_precompile_touch.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/spurious_dragon/eip161_state_trie_clearing/touched_account_emptiness/call_new_account_charge_after_precompile_touch.json");
val defs = mapi (define_test "3169") tests;
