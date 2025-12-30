Theory vfmTestDefs0433[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/expPower256Of256.json";
val defs = mapi (define_test "0433") tests;
