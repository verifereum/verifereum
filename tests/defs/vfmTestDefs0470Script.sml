Theory vfmTestDefs0470[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmLogTest/log0.json";
val defs = mapi (define_test "0470") tests;
