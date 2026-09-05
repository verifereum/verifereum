Theory vfmTestDefs1738[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stShift/shr_minus_1_255/shr_minus_1_255.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stShift/shr_minus_1_255/shr_minus_1_255.json");
val defs = mapi (define_test "1738") tests;
