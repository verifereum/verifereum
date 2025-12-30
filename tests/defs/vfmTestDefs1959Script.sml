Theory vfmTestDefs1959[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrefoundEmptyOOG_Paris.json";
val defs = mapi (define_test "1959") tests;
