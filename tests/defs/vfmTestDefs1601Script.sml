Theory vfmTestDefs1601[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemoryStressTest/create_bounds3/create_bounds3.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemoryStressTest/create_bounds3/create_bounds3.json");
val defs = mapi (define_test "1601") tests;
