Theory vfmTestDefs0136[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/selfdestruct_revert/selfdestruct_not_created_in_same_tx_with_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/selfdestruct_revert/selfdestruct_not_created_in_same_tx_with_revert.json");
val defs = mapi (define_test "0136") tests;
