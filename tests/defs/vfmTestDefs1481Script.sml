Theory vfmTestDefs1481[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRandom2/random_statetest539/random_statetest539.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRandom2/random_statetest539/random_statetest539.json");
val defs = mapi (define_test "1481") tests;
