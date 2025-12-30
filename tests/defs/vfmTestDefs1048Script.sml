Theory vfmTestDefs1048[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/OutOfGasContractCreation.json";
val defs = mapi (define_test "1048") tests;
