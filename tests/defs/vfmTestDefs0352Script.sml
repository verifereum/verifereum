Theory vfmTestDefs0352[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stBugs/random_statetest_default_minus_tue_07_58_41_minus_15153_minus_575192/random_statetest_default_minus_tue_07_58_41_minus_15153_minus_575192.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stBugs/random_statetest_default_minus_tue_07_58_41_minus_15153_minus_575192/random_statetest_default_minus_tue_07_58_41_minus_15153_minus_575192.json");
val defs = mapi (define_test "0352") tests;
