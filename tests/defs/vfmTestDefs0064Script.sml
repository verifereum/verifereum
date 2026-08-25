Theory vfmTestDefs0064[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_blob_hash_versioning_single_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_invalid_blob_hash_versioning_single_tx.json");
val defs = mapi (define_test "0064") tests;
