Theory vfmTestDefs0787[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/CREATE2_ContractSuicideDuringInit_ThenStoreThenReturn.json";
val defs = mapi (define_test "0787") tests;
