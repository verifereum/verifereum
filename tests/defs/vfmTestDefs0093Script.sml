Theory vfmTestDefs0093[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip5656_mcopy/test_no_memory_corruption_on_upper_call_stack_levels.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip5656_mcopy/test_no_memory_corruption_on_upper_call_stack_levels.json");
val defs = mapi (define_test "0093") tests;
