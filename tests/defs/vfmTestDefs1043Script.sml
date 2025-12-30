Theory vfmTestDefs1043[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallContractToCreateContractOOGBonusGas.json";
val defs = mapi (define_test "1043") tests;
