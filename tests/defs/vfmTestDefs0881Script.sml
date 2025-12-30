Theory vfmTestDefs0881[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/CallcodeLoseGasOOG.json";
val defs = mapi (define_test "0881") tests;
