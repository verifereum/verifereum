Theory vfmTestDefs0042[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blob_tx_attribute_calldata_opcodes.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_blob_tx_attribute_calldata_opcodes.json");
val defs = mapi (define_test "0042") tests;
