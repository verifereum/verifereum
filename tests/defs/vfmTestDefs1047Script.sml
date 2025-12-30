Theory vfmTestDefs1047[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallTheContractToCreateEmptyContract.json";
val defs = mapi (define_test "1047") tests;
