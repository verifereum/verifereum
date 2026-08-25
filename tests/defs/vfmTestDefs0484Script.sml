Theory vfmTestDefs0484[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/byteNonConst.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stArgsZeroOneBalance/byteNonConst.json");
val defs = mapi (define_test "0484") tests;
