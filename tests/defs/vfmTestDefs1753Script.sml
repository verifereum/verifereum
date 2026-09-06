Theory vfmTestDefs1753[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSolidityTest/test_structures_and_variabless/test_structures_and_variabless.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSolidityTest/test_structures_and_variabless/test_structures_and_variabless.json");
val defs = mapi (define_test "1753") tests;
