Theory vfmTestDefs1889[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/modexp_modsize0_returndatasize.json";
val defs = mapi (define_test "1889") tests;
