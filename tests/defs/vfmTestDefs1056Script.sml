Theory vfmTestDefs1056[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stPreCompiledContracts2/modexp_0_0_0_20500/modexp_0_0_0_20500.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stPreCompiledContracts2/modexp_0_0_0_20500/modexp_0_0_0_20500.json");
val defs = mapi (define_test "1056") tests;
