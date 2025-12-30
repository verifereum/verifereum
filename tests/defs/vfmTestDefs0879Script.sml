Theory vfmTestDefs0879[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/CallLoseGasOOG.json";
val defs = mapi (define_test "0879") tests;
