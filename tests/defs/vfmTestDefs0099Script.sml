Theory vfmTestDefs0099[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_create_selfdestruct_same_tx_increased_nonce.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip6780_selfdestruct/test_create_selfdestruct_same_tx_increased_nonce.json");
val defs = mapi (define_test "0099") tests;
