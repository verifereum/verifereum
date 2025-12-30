Theory vfmTestDefs2692[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_one_point_with_g1_zero.json";
val defs = mapi (define_test "2692") tests;
