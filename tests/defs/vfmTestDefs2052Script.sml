Theory vfmTestDefs2052[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/TestContractInteraction.json";
val defs = mapi (define_test "2052") tests;
