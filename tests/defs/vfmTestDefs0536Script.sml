Theory vfmTestDefs0536[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBugs/staticcall_createfails.json";
val defs = mapi (define_test "0536") tests;
