Theory vfmTestDefs2080[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStackTests/stackOverflowPUSH.json";
val defs = mapi (define_test "2080") tests;
