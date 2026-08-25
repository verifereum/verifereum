Theory vfmTestDefs0086[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_sufficient_balance_blob_tx_pre_fund_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_sufficient_balance_blob_tx_pre_fund_tx.json");
val defs = mapi (define_test "0086") tests;
