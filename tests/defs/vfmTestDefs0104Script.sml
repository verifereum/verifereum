Theory vfmTestDefs0104[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_reentrancy_selfdestruct_revert.json";
val defs = mapi (define_test "0104") tests;
