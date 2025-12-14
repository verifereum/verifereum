open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0141";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_stack_underflow.json";
val defs = mapi (define_test "0141") tests;
val () = export_theory_no_docs ();
