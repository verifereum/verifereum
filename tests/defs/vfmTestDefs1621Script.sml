Theory vfmTestDefs1621[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemoryStressTest/sload_bounds/sload_bounds.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemoryStressTest/sload_bounds/sload_bounds.json");
val defs = mapi (define_test "1621") tests;
