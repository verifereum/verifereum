Theory vfmTestDefs1190[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRandom/random_statetest246/random_statetest246.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRandom/random_statetest246/random_statetest246.json");
val defs = mapi (define_test "1190") tests;
