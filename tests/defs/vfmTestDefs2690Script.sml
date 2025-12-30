Theory vfmTestDefs2690[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_one_point_insufficient_gas.json";
val defs = mapi (define_test "2690") tests;
