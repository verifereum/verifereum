Theory vfmTestDefs2441[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stShift/shl_minus_1_256/shl_minus_1_256.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stShift/shl_minus_1_256/shl_minus_1_256.json");
val defs = mapi (define_test "2441") tests;
