Theory vfmTestDefs0077[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_static_excess_blob_gas_from_zero_on_blobs_above_target.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_invalid_static_excess_blob_gas_from_zero_on_blobs_above_target.json");
val defs = mapi (define_test "0077") tests;
