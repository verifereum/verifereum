Theory vfmTestDefs1812[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRandom/random_statetest135/random_statetest135.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRandom/random_statetest135/random_statetest135.json");
val defs = mapi (define_test "1812") tests;
