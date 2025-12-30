Theory vfmTestDefs2053[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/TestContractSuicide.json";
val defs = mapi (define_test "2053") tests;
