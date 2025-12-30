Theory vfmTestDefs1412[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest19.json";
val defs = mapi (define_test "1412") tests;
