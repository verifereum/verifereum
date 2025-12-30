Theory vfmTestDefs0877[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/Call1024OOG.json";
val defs = mapi (define_test "0877") tests;
