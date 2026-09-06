Theory vfmTestDefs1720[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stShift/shl01_minus_0101/shl01_minus_0101.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stShift/shl01_minus_0101/shl01_minus_0101.json");
val defs = mapi (define_test "1720") tests;
