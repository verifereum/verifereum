Theory vfmTestDefs1340[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest11.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRandom/randomStatetest11.json");
val defs = mapi (define_test "1340") tests;
