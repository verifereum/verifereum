Theory vfmTestDefs1715[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stShift/shr11/shr11.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stShift/shr11/shr11.json");
val defs = mapi (define_test "1715") tests;
