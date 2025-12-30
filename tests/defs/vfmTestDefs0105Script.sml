Theory vfmTestDefs0105[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_self_destructing_initcode.json";
val defs = mapi (define_test "0105") tests;
