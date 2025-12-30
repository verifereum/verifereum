Theory vfmTestDefs1567[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest359.json";
val defs = mapi (define_test "1567") tests;
