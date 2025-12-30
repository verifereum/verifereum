Theory vfmTestDefs0197[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7918_blob_reserve_price/test_blob_base_fee_with_bpo_transition.json";
val defs = mapi (define_test "0197") tests;
