Theory vfmTestDefs2040[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shr_2^255_256.json";
val defs = mapi (define_test "2040") tests;
