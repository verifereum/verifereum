Theory vfmTestDefs0199[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7918_blob_reserve_price/test_reserve_price_boundary.json";
val defs = mapi (define_test "0199") tests;
