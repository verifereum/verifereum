Theory vfmTestDefs0086[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4844_blobs/blobhash_opcode/blobhash_invalid_blob_index.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4844_blobs/blobhash_opcode/blobhash_invalid_blob_index.json");
val defs = mapi (define_test "0086") tests;
