Theory vfmTestDefs1956[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrefoundCallOOG.json";
val defs = mapi (define_test "1956") tests;
