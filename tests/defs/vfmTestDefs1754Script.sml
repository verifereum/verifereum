Theory vfmTestDefs1754[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSpecialTest/block504980/block504980.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSpecialTest/block504980/block504980.json");
val defs = mapi (define_test "1754") tests;
