Theory vfmTestDefs0109[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_selfdestruct_not_created_in_same_tx_with_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip6780_selfdestruct/test_selfdestruct_not_created_in_same_tx_with_revert.json");
val defs = mapi (define_test "0109") tests;
