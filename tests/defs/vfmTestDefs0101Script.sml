Theory vfmTestDefs0101[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_dynamic_create2_selfdestruct_collision_multi_tx.json";
val defs = mapi (define_test "0101") tests;
