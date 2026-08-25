Theory vfmTestDefs1701[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest458.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRandom2/randomStatetest458.json");
val defs = mapi (define_test "1701") tests;
