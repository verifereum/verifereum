Theory vfmTestDefs0055[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_correct_excess_blob_gas_calculation.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_correct_excess_blob_gas_calculation.json");
val defs = mapi (define_test "0055") tests;
