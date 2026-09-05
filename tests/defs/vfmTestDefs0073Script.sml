Theory vfmTestDefs0073[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4844_blobs/blob_txs/insufficient_balance_blob_tx_combinations.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4844_blobs/blob_txs/insufficient_balance_blob_tx_combinations.json");
val defs = mapi (define_test "0073") tests;
