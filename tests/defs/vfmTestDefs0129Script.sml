Theory vfmTestDefs0129[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/selfdestruct/recreate_self_destructed_contract_different_txs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/selfdestruct/recreate_self_destructed_contract_different_txs.json");
val defs = mapi (define_test "0129") tests;
