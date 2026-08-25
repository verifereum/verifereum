Theory vfmTestDefs0103[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_recreate_self_destructed_contract_different_txs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip6780_selfdestruct/test_recreate_self_destructed_contract_different_txs.json");
val defs = mapi (define_test "0103") tests;
