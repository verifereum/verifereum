Theory vfmTestDefs2417[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stShift/sar_0_256_minus_1/sar_0_256_minus_1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stShift/sar_0_256_minus_1/sar_0_256_minus_1.json");
val defs = mapi (define_test "2417") tests;
