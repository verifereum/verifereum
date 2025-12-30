Theory vfmTestDefs0435[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/mod.json";
val defs = mapi (define_test "0435") tests;
