Theory vfmTestDefs0125[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/selfdestruct/create_multiple_contracts_destroy_one_then_destroy_other_next_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/selfdestruct/create_multiple_contracts_destroy_one_then_destroy_other_next_tx.json");
val defs = mapi (define_test "0125") tests;
