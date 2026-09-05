Theory vfmTestDefs1721[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stShift/shl01_minus_ff/shl01_minus_ff.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stShift/shl01_minus_ff/shl01_minus_ff.json");
val defs = mapi (define_test "1721") tests;
