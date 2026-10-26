Theory vfmTestDefs1596[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemoryStressTest/callcode_bounds2/callcode_bounds2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemoryStressTest/callcode_bounds2/callcode_bounds2.json");
val defs = mapi (define_test "1596") tests;
