Theory vfmTestDefs0068[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_excess_blob_gas_change.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_invalid_excess_blob_gas_change.json");
val defs = mapi (define_test "0068") tests;
