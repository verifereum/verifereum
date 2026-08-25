Theory vfmTestDefs0074[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_post_fork_block_without_blob_fields.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_invalid_post_fork_block_without_blob_fields.json");
val defs = mapi (define_test "0074") tests;
