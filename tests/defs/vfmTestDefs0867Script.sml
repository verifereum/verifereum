Theory vfmTestDefs0867[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateResults.json";
val defs = mapi (define_test "0867") tests;
