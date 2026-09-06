Theory vfmTestDefs0071[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4844_blobs/blob_txs/blob_tx_attribute_value_opcode.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4844_blobs/blob_txs/blob_tx_attribute_value_opcode.json");
val defs = mapi (define_test "0071") tests;
