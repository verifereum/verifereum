Theory vfmTestDefs0046[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blob_type_tx_pre_fork.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_blob_type_tx_pre_fork.json");
val defs = mapi (define_test "0046") tests;
