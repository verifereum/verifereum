Theory vfmTestDefs2446[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stShift/shr_2_255_255/shr_2_255_255.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stShift/shr_2_255_255/shr_2_255_255.json");
val defs = mapi (define_test "2446") tests;
