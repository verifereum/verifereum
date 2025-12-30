Theory vfmTestDefs0889[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/callWithHighValueAndGasOOG.json";
val defs = mapi (define_test "0889") tests;
