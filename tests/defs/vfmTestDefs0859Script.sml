Theory vfmTestDefs0859[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterInitCode.json";
val defs = mapi (define_test "0859") tests;
