Theory vfmTestDefs1774[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/modexp_random_input/modexp_random_input.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/modexp_random_input/modexp_random_input.json");
val defs = mapi (define_test "1774") tests;
