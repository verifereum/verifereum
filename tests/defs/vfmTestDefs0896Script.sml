Theory vfmTestDefs0896[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecallInInitcodeToEmptyContract.json";
val defs = mapi (define_test "0896") tests;
