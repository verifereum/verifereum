Theory vfmTestDefs0872[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryStressTest/dup_bounds/dup_bounds.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryStressTest/dup_bounds/dup_bounds.json");
val defs = mapi (define_test "0872") tests;
