Theory vfmTestDefs2697[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_perturb_g2_by_field_modulus_again.json";
val defs = mapi (define_test "2697") tests;
