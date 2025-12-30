Theory vfmTestDefs0484[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/byteNonConst.json";
val defs = mapi (define_test "0484") tests;
