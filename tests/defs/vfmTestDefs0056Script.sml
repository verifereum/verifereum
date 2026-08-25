Theory vfmTestDefs0056[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_correct_increasing_blob_gas_costs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_correct_increasing_blob_gas_costs.json");
val defs = mapi (define_test "0056") tests;
