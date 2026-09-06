Theory vfmTestDefs1737[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stShift/shr_minus_1_1/shr_minus_1_1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stShift/shr_minus_1_1/shr_minus_1_1.json");
val defs = mapi (define_test "1737") tests;
