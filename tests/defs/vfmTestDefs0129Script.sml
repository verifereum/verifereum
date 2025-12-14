open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0129";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_call_memory_expands_on_early_revert.json";
val defs = mapi (define_test "0129") tests;
val () = export_theory_no_docs ();
