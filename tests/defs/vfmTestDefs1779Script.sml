Theory vfmTestDefs1779[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest550.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRandom2/randomStatetest550.json");
val defs = mapi (define_test "1779") tests;
