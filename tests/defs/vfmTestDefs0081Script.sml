Theory vfmTestDefs0081[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_point_evaluation_precompile_gas_usage.json";
val defs = mapi (define_test "0081") tests;
