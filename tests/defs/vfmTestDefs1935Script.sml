Theory vfmTestDefs1935[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertInCreateInInit_Paris.json";
val defs = mapi (define_test "1935") tests;
