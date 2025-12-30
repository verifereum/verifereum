Theory vfmTestDefs0898[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecallInInitcodeToExistingContractOOG.json";
val defs = mapi (define_test "0898") tests;
