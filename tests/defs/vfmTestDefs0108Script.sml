Theory vfmTestDefs0108[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_selfdestruct_created_same_block_different_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip6780_selfdestruct/test_selfdestruct_created_same_block_different_tx.json");
val defs = mapi (define_test "0108") tests;
