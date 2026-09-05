Theory vfmTestDefs0127[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/selfdestruct/create_selfdestruct_same_tx_increased_nonce.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/selfdestruct/create_selfdestruct_same_tx_increased_nonce.json");
val defs = mapi (define_test "0127") tests;
