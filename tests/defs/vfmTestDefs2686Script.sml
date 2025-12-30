Theory vfmTestDefs2686[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_empty_data.json";
val defs = mapi (define_test "2686") tests;
