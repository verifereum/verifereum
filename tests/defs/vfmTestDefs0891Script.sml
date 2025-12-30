Theory vfmTestDefs0891[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/callcodeWithHighValueAndGasOOG.json";
val defs = mapi (define_test "0891") tests;
