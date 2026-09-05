Theory vfmTestDefs0124[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/selfdestruct/create_and_destroy_multiple_contracts_same_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/selfdestruct/create_and_destroy_multiple_contracts_same_tx.json");
val defs = mapi (define_test "0124") tests;
