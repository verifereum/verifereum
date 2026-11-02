Theory vfmTestDefs2427[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stShift/sar_2_256_minus_1_0/sar_2_256_minus_1_0.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stShift/sar_2_256_minus_1_0/sar_2_256_minus_1_0.json");
val defs = mapi (define_test "2427") tests;
