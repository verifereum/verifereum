Theory vfmTestDefs0094[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4844_blobs/excess_blob_gas/invalid_blob_gas_used_in_header.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4844_blobs/excess_blob_gas/invalid_blob_gas_used_in_header.json");
val defs = mapi (define_test "0094") tests;
