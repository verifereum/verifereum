Theory vfmTestDefs0863[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterInitCodeReturndataSize.json";
val defs = mapi (define_test "0863") tests;
