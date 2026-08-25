Theory vfmTestDefs0075[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_pre_fork_block_with_blob_fields.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_invalid_pre_fork_block_with_blob_fields.json");
val defs = mapi (define_test "0075") tests;
