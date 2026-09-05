Theory vfmTestDefs0097[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4844_blobs/excess_blob_gas/invalid_excess_blob_gas_target_blobs_increase_from_zero.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4844_blobs/excess_blob_gas/invalid_excess_blob_gas_target_blobs_increase_from_zero.json");
val defs = mapi (define_test "0097") tests;
