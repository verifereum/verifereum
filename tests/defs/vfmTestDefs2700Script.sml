Theory vfmTestDefs2700[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_perturb_zeropoint_by_field_modulus.json";
val defs = mapi (define_test "2700") tests;
