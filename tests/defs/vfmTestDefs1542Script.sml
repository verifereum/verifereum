Theory vfmTestDefs1542[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRandom2/random_statetest625/random_statetest625.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRandom2/random_statetest625/random_statetest625.json");
val defs = mapi (define_test "1542") tests;
