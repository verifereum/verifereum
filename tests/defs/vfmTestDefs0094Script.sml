open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0094";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip5656_mcopy/test_no_memory_corruption_on_upper_create_stack_levels.json";
val defs = mapi (define_test "0094") tests;
val () = export_theory_no_docs ();
