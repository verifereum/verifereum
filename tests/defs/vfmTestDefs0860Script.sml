Theory vfmTestDefs0860[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryStressTest/call_bounds2a/call_bounds2a.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryStressTest/call_bounds2a/call_bounds2a.json");
val defs = mapi (define_test "0860") tests;
