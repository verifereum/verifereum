Theory vfmTestDefs1937[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertInStaticCall.json";
val defs = mapi (define_test "1937") tests;
