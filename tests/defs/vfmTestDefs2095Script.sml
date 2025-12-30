Theory vfmTestDefs2095[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CREATE_ContractSuicideDuringInit.json";
val defs = mapi (define_test "2095") tests;
