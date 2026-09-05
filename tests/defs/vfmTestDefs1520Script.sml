Theory vfmTestDefs1520[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRandom2/random_statetest589/random_statetest589.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRandom2/random_statetest589/random_statetest589.json");
val defs = mapi (define_test "1520") tests;
