Theory vfmTestDefs0037[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_invalid_beacon_root_calldata_value.json";
val defs = mapi (define_test "0037") tests;
