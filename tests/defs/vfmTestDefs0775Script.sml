Theory vfmTestDefs0775[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP5656_MCOPY/mcopy_memory_expansion_cost/mcopy_memory_expansion_cost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP5656_MCOPY/mcopy_memory_expansion_cost/mcopy_memory_expansion_cost.json");
val defs = mapi (define_test "0775") tests;
