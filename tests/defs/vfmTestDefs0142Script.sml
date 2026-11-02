Theory vfmTestDefs0142[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists/bal_cross_tx_balance_read_before_later_credit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists/bal_cross_tx_balance_read_before_later_credit.json");
val defs = mapi (define_test "0142") tests;
