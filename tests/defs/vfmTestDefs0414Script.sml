Theory vfmTestDefs0414[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP5656_MCOPY/MCOPY_copy_cost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/Cancun/stEIP5656_MCOPY/MCOPY_copy_cost.json");
val defs = mapi (define_test "0414") tests;
