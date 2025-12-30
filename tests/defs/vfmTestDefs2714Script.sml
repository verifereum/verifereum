Theory vfmTestDefs2714[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/pointAdd.json";
val defs = mapi (define_test "2714") tests;
