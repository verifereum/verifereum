Theory vfmTestDefs0240[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/osaka/eip7823_modexp_upper_bounds/eip_mainnet/modexp_over_boundary.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/osaka/eip7823_modexp_upper_bounds/eip_mainnet/modexp_over_boundary.json");
val defs = mapi (define_test "0240") tests;
