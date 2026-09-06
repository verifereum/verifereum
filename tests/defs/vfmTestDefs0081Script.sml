Theory vfmTestDefs0081[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4844_blobs/blob_txs/sufficient_balance_blob_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4844_blobs/blob_txs/sufficient_balance_blob_tx.json");
val defs = mapi (define_test "0081") tests;
