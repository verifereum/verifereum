Theory vfmTestDefs0471[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmLogTest/log1.json";
val defs = mapi (define_test "0471") tests;
