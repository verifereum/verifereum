Theory vfmTestDefs1955[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrefoundCall.json";
val defs = mapi (define_test "1955") tests;
