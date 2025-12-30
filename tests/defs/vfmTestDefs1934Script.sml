Theory vfmTestDefs1934[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertInCallCode.json";
val defs = mapi (define_test "1934") tests;
