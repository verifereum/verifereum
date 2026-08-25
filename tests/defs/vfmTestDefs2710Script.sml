Theory vfmTestDefs2710[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_two_point_match_5.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_two_point_match_5.json");
val defs = mapi (define_test "2710") tests;
