Theory vfmTestDefs1395[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRandom2/random_statetest430/random_statetest430.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRandom2/random_statetest430/random_statetest430.json");
val defs = mapi (define_test "1395") tests;
