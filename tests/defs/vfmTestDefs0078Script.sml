Theory vfmTestDefs0078[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_tx_blob_count.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_invalid_tx_blob_count.json");
val defs = mapi (define_test "0078") tests;
