Theory vfmTestDefs0061[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_insufficient_balance_blob_tx_combinations.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_insufficient_balance_blob_tx_combinations.json");
val defs = mapi (define_test "0061") tests;
