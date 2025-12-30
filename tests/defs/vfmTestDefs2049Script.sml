Theory vfmTestDefs2049[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/RecursiveCreateContracts.json";
val defs = mapi (define_test "2049") tests;
