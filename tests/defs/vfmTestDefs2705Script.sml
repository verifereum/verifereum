Theory vfmTestDefs2705[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_two_point_fail_2.json";
val defs = mapi (define_test "2705") tests;
