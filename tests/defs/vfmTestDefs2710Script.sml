Theory vfmTestDefs2710[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_two_point_match_5.json";
val defs = mapi (define_test "2710") tests;
