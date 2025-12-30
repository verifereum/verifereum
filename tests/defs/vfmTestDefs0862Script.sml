Theory vfmTestDefs0862[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterInitCodeReturndata3.json";
val defs = mapi (define_test "0862") tests;
