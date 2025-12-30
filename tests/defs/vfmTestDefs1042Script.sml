Theory vfmTestDefs1042[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallContractToCreateContractOOG.json";
val defs = mapi (define_test "1042") tests;
