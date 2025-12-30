Theory vfmTestDefs0534[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBugs/randomStatetestDEFAULT-Tue_07_58_41-15153-575192_london.json";
val defs = mapi (define_test "0534") tests;
