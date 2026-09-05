Theory vfmTestDefs0774[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP5656_MCOPY/mcopy_copy_cost/mcopy_copy_cost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP5656_MCOPY/mcopy_copy_cost/mcopy_copy_cost.json");
val defs = mapi (define_test "0774") tests;
