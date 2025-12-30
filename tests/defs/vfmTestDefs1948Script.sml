Theory vfmTestDefs1948[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertOpcodeWithBigOutputInInit.json";
val defs = mapi (define_test "1948") tests;
