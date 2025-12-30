Theory vfmTestDefs0441[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/smod.json";
val defs = mapi (define_test "0441") tests;
