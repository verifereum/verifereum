Theory vfmTestDefs0907[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/CallGoesOOGOnSecondLevel2.json";
val defs = mapi (define_test "0907") tests;
