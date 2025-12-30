Theory vfmTestDefs0040[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_tx_to_beacon_root_contract.json";
val defs = mapi (define_test "0040") tests;
