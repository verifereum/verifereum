Theory vfmTestDefs2701[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_perturb_zeropoint_by_one.json";
val defs = mapi (define_test "2701") tests;
