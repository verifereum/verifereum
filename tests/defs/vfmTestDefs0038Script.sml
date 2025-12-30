Theory vfmTestDefs0038[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_multi_block_beacon_root_timestamp_calls.json";
val defs = mapi (define_test "0038") tests;
