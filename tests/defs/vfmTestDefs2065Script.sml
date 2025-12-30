Theory vfmTestDefs2065[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/deploymentError.json";
val defs = mapi (define_test "2065") tests;
