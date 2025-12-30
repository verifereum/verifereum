Theory vfmTestDefs0097[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_calling_from_pre_existing_contract_to_new_contract.json";
val defs = mapi (define_test "0097") tests;
