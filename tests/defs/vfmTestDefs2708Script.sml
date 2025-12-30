Theory vfmTestDefs2708[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_two_point_match_3.json";
val defs = mapi (define_test "2708") tests;
