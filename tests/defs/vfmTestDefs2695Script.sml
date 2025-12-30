Theory vfmTestDefs2695[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_perturb_g2_by_curve_order.json";
val defs = mapi (define_test "2695") tests;
