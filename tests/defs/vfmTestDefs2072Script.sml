Theory vfmTestDefs2072[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/sha3_deja.json";
val defs = mapi (define_test "2072") tests;
