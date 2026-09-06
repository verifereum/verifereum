Theory vfmTestDefs0112[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip5656_mcopy/mcopy_contexts/no_memory_corruption_on_upper_call_stack_levels.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip5656_mcopy/mcopy_contexts/no_memory_corruption_on_upper_call_stack_levels.json");
val defs = mapi (define_test "0112") tests;
