Theory vfmTestDefs2702[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_three_point_fail_1.json";
val defs = mapi (define_test "2702") tests;
