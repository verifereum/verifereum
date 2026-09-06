Theory vfmTestDefs0068[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4844_blobs/blob_txs/blob_tx_attribute_calldata_opcodes.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4844_blobs/blob_txs/blob_tx_attribute_calldata_opcodes.json");
val defs = mapi (define_test "0068") tests;
