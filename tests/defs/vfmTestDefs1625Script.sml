Theory vfmTestDefs1625[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemoryStressTest/static_call_bounds2a/static_call_bounds2a.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemoryStressTest/static_call_bounds2a/static_call_bounds2a.json");
val defs = mapi (define_test "1625") tests;
