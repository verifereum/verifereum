Theory vfmTestDefs0036[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_calldata_lengths.json";
val defs = mapi (define_test "0036") tests;
