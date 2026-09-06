Theory vfmTestDefs0120[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/journal_revert/selfdestruct_balance_transfer_reverted.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/journal_revert/selfdestruct_balance_transfer_reverted.json");
val defs = mapi (define_test "0120") tests;
