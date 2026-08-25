Theory vfmTestDefs1326[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/modexp_0_0_0_22000.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stPreCompiledContracts2/modexp_0_0_0_22000.json");
val defs = mapi (define_test "1326") tests;
