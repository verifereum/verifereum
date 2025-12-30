Theory vfmTestDefs0885[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/callOutput2.json";
val defs = mapi (define_test "0885") tests;
