Theory vfmTestDefs0473[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmLogTest/log3.json";
val defs = mapi (define_test "0473") tests;
