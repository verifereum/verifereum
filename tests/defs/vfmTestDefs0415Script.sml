Theory vfmTestDefs0415[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP5656_MCOPY/MCOPY_memory_expansion_cost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/Cancun/stEIP5656_MCOPY/MCOPY_memory_expansion_cost.json");
val defs = mapi (define_test "0415") tests;
