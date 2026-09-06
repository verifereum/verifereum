Theory vfmTestDefs1710[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stShift/sar_2_255_minus_1_248/sar_2_255_minus_1_248.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stShift/sar_2_255_minus_1_248/sar_2_255_minus_1_248.json");
val defs = mapi (define_test "1710") tests;
