Theory vfmTestDefs2007[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^255-1_248.json";
val defs = mapi (define_test "2007") tests;
