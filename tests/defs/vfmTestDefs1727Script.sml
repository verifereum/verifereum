Theory vfmTestDefs1727[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stShift/shl_minus_1_255/shl_minus_1_255.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stShift/shl_minus_1_255/shl_minus_1_255.json");
val defs = mapi (define_test "1727") tests;
