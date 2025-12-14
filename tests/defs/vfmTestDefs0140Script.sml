open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0140";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_stack_overflow.json";
val defs = mapi (define_test "0140") tests;
val () = export_theory_no_docs ();
