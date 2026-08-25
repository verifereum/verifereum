Theory vfmTestDefs0084[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_reject_valid_full_blob_in_block_rlp.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_reject_valid_full_blob_in_block_rlp.json");
val defs = mapi (define_test "0084") tests;
