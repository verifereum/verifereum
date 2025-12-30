Theory vfmTestDefs2071[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/selfdestructEIP2929.json";
val defs = mapi (define_test "2071") tests;
