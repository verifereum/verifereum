Theory vfmTestDefs0426[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/addmod.json";
val defs = mapi (define_test "0426") tests;
