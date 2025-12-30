Theory vfmTestDefs2038[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shr_2^255_1.json";
val defs = mapi (define_test "2038") tests;
