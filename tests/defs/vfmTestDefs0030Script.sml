Theory vfmTestDefs0030[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_beacon_root_contract_calls.json";
val defs = mapi (define_test "0030") tests;
