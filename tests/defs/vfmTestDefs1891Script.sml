Theory vfmTestDefs1891[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_afterFailing_create.json";
val defs = mapi (define_test "1891") tests;
