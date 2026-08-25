Theory vfmTestDefs0045[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blob_tx_attribute_value_opcode.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_blob_tx_attribute_value_opcode.json");
val defs = mapi (define_test "0045") tests;
