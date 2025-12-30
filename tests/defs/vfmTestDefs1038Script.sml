Theory vfmTestDefs1038[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stHomesteadSpecific/createContractViaContractOOGInitCode.json";
val defs = mapi (define_test "1038") tests;
