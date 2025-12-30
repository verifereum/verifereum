Theory vfmTestDefs0900[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecallSenderCheck.json";
val defs = mapi (define_test "0900") tests;
