Theory vfmTestDefs2152[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallRecursiveBomb1.json";
val defs = mapi (define_test "2152") tests;
