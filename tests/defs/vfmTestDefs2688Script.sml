Theory vfmTestDefs2688[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_inputs.json";
val defs = mapi (define_test "2688") tests;
