Theory vfmTestDefs0171[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7823_modexp_upper_bounds/test_modexp_upper_bounds_fork_transition.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7823_modexp_upper_bounds/test_modexp_upper_bounds_fork_transition.json");
val defs = mapi (define_test "0171") tests;
