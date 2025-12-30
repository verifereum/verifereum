Theory vfmTestDefs2014[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^255_257.json";
val defs = mapi (define_test "2014") tests;
