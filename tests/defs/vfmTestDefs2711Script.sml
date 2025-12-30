Theory vfmTestDefs2711[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_two_point_oog.json";
val defs = mapi (define_test "2711") tests;
