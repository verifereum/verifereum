Theory vfmTestDefs1439[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest217.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRandom/randomStatetest217.json");
val defs = mapi (define_test "1439") tests;
