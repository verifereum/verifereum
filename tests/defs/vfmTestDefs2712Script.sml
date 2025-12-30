Theory vfmTestDefs2712[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_two_points_with_one_g2_zero.json";
val defs = mapi (define_test "2712") tests;
