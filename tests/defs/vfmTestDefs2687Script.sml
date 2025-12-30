Theory vfmTestDefs2687[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_empty_data_insufficient_gas.json";
val defs = mapi (define_test "2687") tests;
