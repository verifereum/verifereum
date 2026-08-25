Theory vfmTestDefs2696[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_perturb_g2_by_field_modulus.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_perturb_g2_by_field_modulus.json");
val defs = mapi (define_test "2696") tests;
