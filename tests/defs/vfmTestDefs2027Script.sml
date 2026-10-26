Theory vfmTestDefs2027[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRandom/random_statetest41/random_statetest41.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRandom/random_statetest41/random_statetest41.json");
val defs = mapi (define_test "2027") tests;
