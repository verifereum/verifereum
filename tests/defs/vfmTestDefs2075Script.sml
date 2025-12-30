Theory vfmTestDefs2075[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStackTests/stackOverflow.json";
val defs = mapi (define_test "2075") tests;
