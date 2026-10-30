Theory vfmTestDefs2207[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRandom2/random_statetest556/random_statetest556.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRandom2/random_statetest556/random_statetest556.json");
val defs = mapi (define_test "2207") tests;
