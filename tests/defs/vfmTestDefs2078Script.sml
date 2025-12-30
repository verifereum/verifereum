Theory vfmTestDefs2078[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStackTests/stackOverflowM1DUP.json";
val defs = mapi (define_test "2078") tests;
