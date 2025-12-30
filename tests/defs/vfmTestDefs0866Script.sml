Theory vfmTestDefs0866[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterMaxCodesize.json";
val defs = mapi (define_test "0866") tests;
