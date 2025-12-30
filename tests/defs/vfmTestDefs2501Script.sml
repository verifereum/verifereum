Theory vfmTestDefs2501[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransitionTest/delegatecallBeforeTransition.json";
val defs = mapi (define_test "2501") tests;
