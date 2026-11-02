Theory vfmTestDefs0961[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip4844_blobs/excess_blob_gas/correct_excess_blob_gas_calculation.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip4844_blobs/excess_blob_gas/correct_excess_blob_gas_calculation.json");
val defs = mapi (define_test "0961") tests;
