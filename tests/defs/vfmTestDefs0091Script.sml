Theory vfmTestDefs0091[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4844_blobs/excess_blob_gas/correct_decreasing_blob_gas_costs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4844_blobs/excess_blob_gas/correct_decreasing_blob_gas_costs.json");
val defs = mapi (define_test "0091") tests;
