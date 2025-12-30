Theory vfmTestDefs2694[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_one_point_with_g2_zero_and_g1_invalid.json";
val defs = mapi (define_test "2694") tests;
