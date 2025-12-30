Theory vfmTestDefs2497[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransitionTest/createNameRegistratorPerTxsAt.json";
val defs = mapi (define_test "2497") tests;
