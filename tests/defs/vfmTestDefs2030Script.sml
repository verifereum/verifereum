Theory vfmTestDefs2030[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shl_2^255-1_1.json";
val defs = mapi (define_test "2030") tests;
