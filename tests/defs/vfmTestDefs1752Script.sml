Theory vfmTestDefs1752[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSolidityTest/test_overflow/test_overflow.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSolidityTest/test_overflow/test_overflow.json");
val defs = mapi (define_test "1752") tests;
