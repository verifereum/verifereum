open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0085";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip5656_mcopy/mcopy_contexts/no_memory_corruption_on_upper_call_stack_levels.json";
val defs = mapi (define_test "0085") tests;
val () = export_theory_no_docs ();
