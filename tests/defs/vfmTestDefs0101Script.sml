Theory vfmTestDefs0101[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4844_blobs/excess_blob_gas/invalid_static_excess_blob_gas_from_zero_on_blobs_above_target.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4844_blobs/excess_blob_gas/invalid_static_excess_blob_gas_from_zero_on_blobs_above_target.json");
val defs = mapi (define_test "0101") tests;
