Theory vfmTestDefs2058[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/TestStructuresAndVariabless.json";
val defs = mapi (define_test "2058") tests;
