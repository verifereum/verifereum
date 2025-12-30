Theory vfmTestDefs2097[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CREATE_ContractSuicideDuringInit_WithValue.json";
val defs = mapi (define_test "2097") tests;
