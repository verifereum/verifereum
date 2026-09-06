Theory vfmTestDefs1735[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stShift/shr_2_255_257/shr_2_255_257.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stShift/shr_2_255_257/shr_2_255_257.json");
val defs = mapi (define_test "1735") tests;
