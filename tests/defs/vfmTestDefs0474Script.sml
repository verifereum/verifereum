Theory vfmTestDefs0474[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmLogTest/log4.json";
val defs = mapi (define_test "0474") tests;
