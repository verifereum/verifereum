Theory vfmTestDefs2069[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSpecialTest/makeMoney.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSpecialTest/makeMoney.json");
val defs = mapi (define_test "2069") tests;
