Theory vfmTestDefs2694[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_one_point_with_g2_zero_and_g1_invalid.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_one_point_with_g2_zero_and_g1_invalid.json");
val defs = mapi (define_test "2694") tests;
