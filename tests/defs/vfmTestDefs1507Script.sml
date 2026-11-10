Theory vfmTestDefs1507[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP5656_MCOPY/mcopy/mcopy.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP5656_MCOPY/mcopy/mcopy.json");
val defs = mapi (define_test "1507") tests;
