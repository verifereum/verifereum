Theory vfmTestDefs0168[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7823_modexp_upper_bounds/test_modexp_boundary.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7823_modexp_upper_bounds/test_modexp_boundary.json");
val defs = mapi (define_test "0168") tests;
