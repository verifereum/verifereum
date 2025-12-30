Theory vfmTestDefs0102[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_dynamic_create2_selfdestruct_collision_two_different_transactions.json";
val defs = mapi (define_test "0102") tests;
