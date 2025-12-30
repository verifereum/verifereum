Theory vfmTestDefs1045[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallContractToCreateContractWhichWouldCreateContractInInitCode.json";
val defs = mapi (define_test "1045") tests;
