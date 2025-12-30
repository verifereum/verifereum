Theory vfmTestDefs2002[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar01.json";
val defs = mapi (define_test "2002") tests;
