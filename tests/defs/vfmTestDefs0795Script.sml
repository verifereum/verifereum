Theory vfmTestDefs0795[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/Create2OOGafterInitCodeReturndata.json";
val defs = mapi (define_test "0795") tests;
